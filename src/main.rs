#![feature(box_syntax, untagged_unions, try_trait)]

use xml::attribute::*;
use xml::*;
extern crate vk_parse;
use fxhash::*;
use inflector::Inflector;
use std::fs::File;
use std::io::BufReader;

use Default;

use xml::reader::{EventReader, XmlEvent};

#[derive(Default, Debug, Eq, PartialEq, Hash)]
struct Enum {
    name: String,
    bitmask: bool,
    members: Vec<(String, EnumValue)>,
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
enum EnumValue {
    Bitpos(i64),
    Value(Value),
    Alias(Box<(String, EnumValue)>),
}

impl EnumValue {
    pub fn get_val(&self) -> i64 {
        match self {
            EnumValue::Bitpos(v) => 1 << v,
            EnumValue::Value(v) => v.to_f64() as i64,
            EnumValue::Alias(v) => v.1.get_val(),
        }
    }

    pub fn tystr(&self) -> &str {
        match self {
            EnumValue::Value(v) => match v {
                Value::u32(_) => "u32",
                Value::u64(_) => "u64",
                Value::i64(_) => "usize",
                Value::f32(_) => "f32",
            },
            EnumValue::Alias(v) => v.1.tystr(),
            _ => unreachable!(),
        }
    }
}

#[derive(Default, Debug, Eq, PartialEq, Hash)]
pub struct Struct {
    name: String,
    members: Vec<StructMember>,
    retonly: bool,
    stype: String,
    extends: String,
}

#[derive(Default, Debug, Eq, PartialEq, Hash)]
pub struct StructMember {
    name: String,
    ty: String,
    cv: String,
    arr: Vec<Len>,
    bit: Option<u32>,
    len: Expr,
    is_len: bool,
    inner_len: bool,
    null_term: bool,
}

#[derive(Debug)]
pub struct FnPtr {
    name: String,
    ret: String,
    ret_cv: String,
    args: Vec<StructMember>,
}

impl StructMember {
    pub fn is_mut(&self) -> bool {
        self.cv.find("m").is_some()
    }
    pub fn alloc_cb(&self) -> bool {
        self.ty == "VkAllocationCallbacks"
    }
    pub fn out_ty(&self) -> String {
        if self.len != Expr::Void {
            match self.cv.as_str() {
                "pm" => format!("Vec<{}>", self.ty),
                _ => unreachable!(),
            }
        } else {
            match self.cv.as_str() {
                "pm" => self.ty.to_string(),
                "pmpm" => format!("*mut {}", self.ty),
                _ => unreachable!(),
            }
        }
    }

    pub fn ty(&self, p: bool) -> String {
        let mut ty = format!(
            "{}{}",
            if p {
                self.cv.replace("pm", "*mut ").replace("pc", "*const ")
            } else {
                self.cv.replace("pm", "&mut ").replace("pc", "&")
            },
            self.ty
        );
        for len in self.arr.iter() {
            ty = format!(
                "[{}; {}]",
                ty,
                match len {
                    Len::i64(i) => i.to_string(),
                    Len::apic(s) => format!("VulkanConstants::{}", &s[3..]),
                }
            );
        }
        ty
    }

    pub fn write(&self, p: bool) {
        println!(
            "\t{}{}: {},",
            if p { "pub " } else { "" },
            self.name,
            self.ty(true)
        );
    }
    pub fn fn_ty(&self) -> String {
        if self.ty.starts_with("foreign") {
            eprintln!("{}", self.ty(true));
            return self.ty(true);
        }
        if self.null_term && self.len == Expr::Void {
            "&str".to_string()
        } else if self.len != Expr::Void {
            let (ty, s) = match self.cv.as_str() {
                "pc" => (format!("&[{}]", self.ty), format!("&{}", self.ty)),
                "pcpc" => (format!("&[*const {}]", self.ty), format!("&{}", self.ty)),
                "pm" => (format!("&mut [{}]", self.ty), format!("&mut {}", self.ty)),
                _ => unreachable!(),
            };
            ty
        } else {
            match self.cv.as_str() {
                "pcpc" => format!("&*const {}", self.ty),
                _ => self.ty(false),
            }
        }
    }
    pub fn setter(&self) {
        if self.name == "s_type" {
            return;
        }
        let mut ismut = false;
        let mut isstr = self.null_term && self.len == Expr::Void;
        let mut second = None;
        let ty = if self.ty.contains("foreign") {
            self.ty(true)
        } else if isstr {
            "&str".to_string()
        } else if self.len != Expr::Void {
            let (ty, s) = match self.cv.as_str() {
                "pc" => (format!("&[{}]", self.ty), format!("&{}", self.ty)),
                "pcpc" => (format!("&[*const {}]", self.ty), format!("&{}", self.ty)),
                "pm" => {
                    ismut = true;
                    (format!("&mut [{}]", self.ty), format!("&mut {}", self.ty))
                }
                _ => unreachable!(),
            };
            second = Some(s);
            ty
        } else {
            match self.cv.as_str() {
                "pcpc" => format!("&*const {}", self.ty),
                _ => self.ty(false),
            }
        };
        println!(
            "\tpub fn {0}(&mut self, {0}: {1}) -> &mut Self {{",
            self.name, ty
        );
        if self.len != Expr::Void || isstr {
            println!(
                "\t\tself.{0} = {0}.as_{1}ptr();",
                self.name,
                if ismut { "mut_" } else { "" }
            );
        } else {
            println!("\t\tself.{0} = {0};", self.name);
        }
        let mut length = "";
        if let Some(var) = self.len.has_var() {
            let mut len = format!("{} as _", self.len.eval_var(format!("{}.len()", self.name)));
            length = var;
            println!("\t\tself.{} = {};", var, len);
        }
        println!("\t\tself\n\t}}");

        if let Some(s) = second {
            let singular = self.name.to_pascal_case().to_singular().to_snake_case();
            if singular != self.name && !length.is_empty() && !self.null_term {
                println!(
                    "\tpub fn {0}(&mut self, {0}: {1}) -> &mut Self {{",
                    singular, s
                );
                println!("\t\tself.{} = {};", self.name, singular);
                println!("\t\tself.{} = {};", length, 1);
                println!("\t\tself\n\t}}");
            }
        }
    }
}

#[derive(Default, Debug)]
struct Handle {
    name: String,
    cmds: Vec<FnPtr>,
}

impl Handle {
    pub fn write(&self) {
        println!("impl {} for {} {{", &self.name[2..], self.name);
        println!("\tfn raw_handle(&self) -> {} {{\n\t\t*self\n\t}}\n}}", self.name);
        println!("pub trait {} {{", &self.name[2..]);
        println!("\tfn raw_handle(&self) -> {};", self.name);
        for cmd in self.cmds.iter() {
            cmd.write(&["Cmd", &self.name[2..]], &self.name);
        }
        println!("}}");
    }
}

impl FnPtr {
    pub fn write(&self, h: &[&str], handle: &str) {
        let mut name = self.name.replace("vk", "");
        for s in h {
            name = name.replace(s, "");
        }
        let mut args = vec![];
        let mut outs = vec![];
        let mut double_call = false;
        let mut lenc = 0;
        let res = self.ret == "VkResult";
        let slf = self.ret == "c_void";
        let mut locals1 = vec![];
        let mut locals2 = vec![];
        let mut push1 = vec![format!("self.raw_handle()")];
        let mut push2 = vec![format!("self.raw_handle()")];
        let mut out_vars = vec![];

        for a in self.args.iter() {
            if !a.is_mut() && a.is_len {
                lenc += 1;
                push1.push(a.name.to_string());
                push2.push(a.name.to_string());
            }
            if a.is_mut() && a.is_len {
                double_call = true;
                locals1.push(("count".to_string(), 0.to_string()));
                push1.push("&mut count".to_string());
                push2.push("&mut count".to_string());
            } else if a.alloc_cb() {
                push1.push("null()".to_string());
                push2.push("null()".to_string());
            }
            if !a.is_len && !a.alloc_cb() {
                if a.is_mut() {
                    outs.push(a);
                    out_vars.push(a.name.clone());
                    if a.ty == "c_void" || a.ty.contains("foreign") {
                        //eprintln!("{}", self.name);
                        return;
                    }
                    //vkCreateRayTracingPipelinesNV
                    if a.len != Expr::Void {
                        if double_call {
                            push1.push(format!("null_mut()"));
                            locals2.push((
                                format!("{}", a.name),
                                "vec![zeroed(); count as usize]".to_string(),
                            ));
                        } else {
                            push1.push(format!("{}.as_mut_ptr()", a.name));
                            locals1.push((
                                format!("{}", a.name),
                                format!(
                                    "vec![zeroed(); {} as usize]",
                                    match &a.len {
                                        Expr::Accessor(l, r) => format!("{}.{}", l, r),
                                        _ => {
                                            format!(
                                                "{}.len()",
                                                self.args
                                                    .iter()
                                                    .find(|b| a.name != b.name && b.len == a.len)
                                                    .unwrap()
                                                    .name
                                            )
                                        }
                                    }
                                ),
                            ));
                        }
         
                        push2.push(format!("{}.as_mut_ptr()", a.name));
                    } else {
                        locals1.push((a.name.clone(), "zeroed()".to_string()));
                        push1.push(format!("&mut {}", a.name));
                        push2.push(format!("&mut {}", a.name));
                    }
                } else {
                    if a.len != Expr::Void || a.null_term {
                        push1.push(format!("{}.as_ptr()", a.name));
                        push2.push(format!("{}.as_ptr()", a.name));
                        if !a.null_term {
                            let len = a.len.has_var().expect(&a.name);
                            if let Some(ll) = push1
                                .iter_mut()
                                .zip(push2.iter_mut())
                                .find(|(a, b)| a.as_str() == len)
                            {
                                *ll.0 = format!("{}.len() as _", a.name);
                                *ll.1 = ll.0.clone();
                            }
                        }
                    } else {
                        push1.push(format!("{}", a.name));
                        push2.push(format!("{}", a.name));
                    }
                    args.push(a);
                }
            }
        }
        let mut out = outs.iter().map(|t| t.out_ty()).collect::<Vec<_>>();
        let forward = match self.ret.as_str() {
            "c_void" => false,
            "VkResult" => outs.is_empty(),
            _ => {
                out = vec![self.ret.clone()];
                true
            }
        };
        let mut out = if out.len() > 1 {
            format!("({})", out.join(", "))
        } else {
            out.join(", ")
        };
        let out = match self.ret.as_str() {
            "VkResult" => {
                if outs.is_empty() {
                    "VkResult".to_string()
                } else {
                    format!("Result<{}>", out)
                }
            }
            "c_void" => {
                if out.is_empty() {
                    out_vars = vec!["self".to_string()];
                    "&Self".to_string()
                } else {
                    out
                }
            }
            _ => out,
        };

        println!(
            "\tfn {}(&self, {}) -> {} {{",
            name.to_snake_case(),
            //self.name,
            args.iter()
                .map(|a| format!("{}: {}", a.name, a.fn_ty()))
                .collect::<Vec<_>>()
                .join(", "),
            out
        );
        println!(
            "\t\textern \"C\" {{ fn {} (handle: {}, {}) -> {}; }}",
            self.name,
            handle,
            self.args
                .iter()
                .map(|a| format!("{}: {}", a.name, a.ty(true)))
                .collect::<Vec<_>>()
                .join(", "),
            self.ret
        );
        println!("\t\tunsafe {{");
        for (var, val) in locals1 {
            println!("\t\t\tlet mut {} = {};", var, val);
        }

        if forward {
            println!("\t\t\t{}({})", self.name, push1.join(", "));
        } else {
            println!(
                "\t\t\t{}({}){};",
                self.name,
                push1.join(", "),
                if res { "?" } else { "" }
            );
        }

        for (var, val) in locals2 {
            println!("\t\t\tlet mut {} = {};", var, val);
        }
        if double_call {
            println!(
                "\t\t\t{}({}){};",
                self.name,
                push2.join(", "),
                if res { "?" } else { "" }
            );
        }
        if !forward {
            if !out_vars.is_empty() {
                let re = format!("{}", out_vars.join(", "));
                let re = if out_vars.len() > 1 {
                    format!("({})", re)
                } else {
                    re
                };
                if res {
                    println!("\t\t\tOk({})", re);
                } else {
                    println!("\t\t\t{}", re);
                }
            } else {
                println!("\t\t\tself");
            }
        }
        println!("\t\t}}\n\t}}");
    }
}

#[derive(Debug, Default, Eq, PartialEq, Hash)]
pub struct XmlNode {
    parent: usize,
    name: String,
    attr: Vec<(String, String)>,
    children: Vec<XmlChild>,
}

impl XmlNode {
    pub fn show_self(&self, d: &str) {
        println!("{}{}", d, self.name);
        for (k, v) in self.attr.iter() {
            println!("{}\t[{} = {}]", d, k, v);
        }
    }

    pub fn show(&self, d: &str) {
        self.show_self(&d);
        for c in self.children.iter() {
            match c {
                XmlChild::Node(c) => c.show(&[d, "\t"].concat()),
                XmlChild::Str(s) => {
                    println!("{}\t\"{}\"", d, s);
                }
            }
        }
    }

    pub fn children(&self) -> Vec<&XmlNode> {
        self.children
            .iter()
            .filter_map(|c| match c {
                XmlChild::Node(n) => Some(n.as_ref()),
                _ => None,
            })
            .collect()
    }

    pub fn cpp_type(&self) -> String {
        self.children
            .iter()
            .map(|c| match c {
                XmlChild::Node(c) => c.get_str(),
                XmlChild::Str(s) => s,
            })
            .collect::<Vec<_>>()
            .join(" ")
    }

    pub fn visit<F: Fn(&XmlNode, &str), F2: Fn(&XmlNode) -> bool>(&self, s: &str, f: &F, f2: &F2) {
        if f2(self) {
            f(self, s);
            for c in self.children() {
                c.visit(&[s, "\t"].concat(), f, f2);
            }
        }
    }

    pub fn find_attr(&self, attr: &str) -> Option<&str> {
        self.attr
            .iter()
            .find(|(k, v)| k == attr)
            .map(|(k, v)| v.as_str())
    }
    pub fn find_child(&self, c: &str) -> Option<&XmlNode> {
        self.children().into_iter().find(|n| n.name == c)
    }
    pub fn get_str(&self) -> &str {
        match self.children.as_slice() {
            [XmlChild::Str(s)] => s,
            _ => unreachable!(),
        }
    }
    pub fn show_if(&self, k: &str, v: &str) {
        if Some(v) == self.find_attr(k) {
            self.show("")
        }
    }

    pub fn get_attr(&self, map: &mut Map<String, Set<String>>) {
        for (k, v) in self.attr.iter() {
            map.entry(k.clone()).or_default().insert(v.clone());
        }
        // for c in self.children() {
        //     c.get_attr(map)
        // }
    }
}

#[derive(Debug, Eq, PartialEq, Hash)]
enum XmlChild {
    Node(Box<XmlNode>),
    Str(String),
}

fn parser_xml() -> Box<XmlNode> {
    fn new_node(name: String, attr: Vec<OwnedAttribute>) -> Box<XmlNode> {
        let mut node = box XmlNode::default();
        node.name = name;
        node.attr = attr
            .into_iter()
            .filter_map(|a| {
                if a.name.local_name != "comment" {
                    Some((a.name.local_name, a.value))
                } else {
                    None
                }
            })
            .collect();
        node
    }
    unsafe {
        let mut root = box XmlNode::default();
        let mut curr_node = None;
        let mut comment = false;
        for e in EventReader::new(BufReader::new(File::open("vk.xml").unwrap())) {
            match e.unwrap() {
                XmlEvent::StartElement {
                    name, attributes, ..
                } => {
                    if name.local_name == "comment" {
                        comment = true;
                        continue;
                    }
                    if curr_node.is_some() {
                        let mut node = new_node(name.local_name, attributes);
                        node.parent = curr_node.unwrap();
                        let mut c = transmute::<usize, &mut XmlNode>(curr_node.unwrap());
                        curr_node = Some(transmute(node.as_ref()));
                        c.children.push(XmlChild::Node(node));
                    } else {
                        {
                            root = new_node(name.local_name, attributes);
                            curr_node = Some(transmute(root.as_ref()));
                        }
                    }
                }
                XmlEvent::EndElement { name } => {
                    if name.local_name == "comment" {
                        comment = false;
                        continue;
                    }
                    curr_node = Some(transmute::<usize, &XmlNode>(curr_node.unwrap()).parent);
                }
                XmlEvent::Characters(s) => {
                    if !comment {
                        transmute::<usize, &mut XmlNode>(curr_node.unwrap())
                            .children
                            .push(XmlChild::Str(s.trim().to_string()));
                    }
                }
                _ => (),
            }
        }
        root
    }
}

type Set<T> = FxHashSet<T>;
type Map<T, U> = FxHashMap<T, U>;

fn find_node<'a, F: Fn(&'a XmlNode) -> bool>(root: &'a XmlNode, f: &F) -> Option<&'a XmlNode> {
    for c in root.children() {
        if f(c) {
            return Some(c);
        }
    }
    None
}

#[derive(Debug, Eq, PartialEq, Hash)]
pub enum Len {
    i64(i64),
    apic(String),
}

fn main() {
    let reg = parser_xml();
    let (mut enums, apic) = parse_enums(&reg);
    let (structs, unions, typedefs, handles, fnptrs, statics) = parse_structs(&reg);
    enums.iter_mut().for_each(|mut e| e.rename());
    write_other(&typedefs, &handles, &fnptrs, &statics);
    write_enums(&enums, &apic);
    write_structs(&structs, &unions)
    //reg.find_child("commands").unwrap().show("");
}

fn write_other(
    typedefs: &Vec<(String, String)>,
    handles: &Vec<Handle>,
    fnptrs: &Vec<FnPtr>,
    statics: &Vec<FnPtr>,
) {
    let foriegn32 = vec!["xcb_visualid_t", "xcb_window_t", "DWORD", "zx_handle_t"];
    let foriegn64 = vec![
        "xcb_connection_t",
        "VisualID",
        "Window",
        "GgpStreamDescriptor",
        "GgpFrameToken",
        "IDirectFB",
        "IDirectFBSurface",
        "HINSTANCE",
        "HWND",
        "HMONITOR",
        "HANDLE",
        "LPCWSTR",
    ];
    let c_voids = vec![
        "SECURITY_ATTRIBUTES",
        "RROutput",
        "wl_display",
        "Display",
        "wl_surface",
    ];
    let ext = vec![
        "VK_LAYER_KHRONOS_validation",
        "VK_KHR_16bit_storage",
        "VK_KHR_8bit_storage",
        "VK_KHR_android_surface",
        "VK_KHR_bind_memory2",
        "VK_KHR_buffer_device_address",
        "VK_KHR_copy_commands2",
        "VK_KHR_create_renderpass2",
        "VK_KHR_dedicated_allocation",
        "VK_KHR_deferred_host_operations",
        "VK_KHR_depth_stencil_resolve",
        "VK_KHR_descriptor_update_template",
        "VK_KHR_device_group",
        "VK_KHR_device_group_creation",
        "VK_KHR_display",
        "VK_KHR_display_swapchain",
        "VK_KHR_draw_indirect_count",
        "VK_KHR_driver_properties",
        "VK_KHR_external_fence",
        "VK_KHR_external_fence_capabilities",
        "VK_KHR_external_fence_fd",
        "VK_KHR_external_fence_win32",
        "VK_KHR_external_memory",
        "VK_KHR_external_memory_capabilities",
        "VK_KHR_external_memory_fd",
        "VK_KHR_external_memory_win32",
        "VK_KHR_external_semaphore",
        "VK_KHR_external_semaphore_capabilities",
        "VK_KHR_external_semaphore_fd",
        "VK_KHR_external_semaphore_win32",
        "VK_KHR_fragment_shading_rate",
        "VK_KHR_get_display_properties2",
        "VK_KHR_get_memory_requirements2",
        "VK_KHR_get_physical_device_properties2",
        "VK_KHR_get_surface_capabilities2",
        "VK_KHR_image_format_list",
        "VK_KHR_imageless_framebuffer",
        "VK_KHR_incremental_present",
        "VK_KHR_maintenance1",
        "VK_KHR_maintenance2",
        "VK_KHR_maintenance3",
        "VK_KHR_multiview",
        "VK_KHR_performance_query",
        "VK_KHR_pipeline_executable_properties",
        "VK_KHR_pipeline_library",
        "VK_KHR_portability_subset",
        "VK_KHR_push_descriptor",
        "VK_KHR_ray_tracing",
        "VK_KHR_relaxed_block_layout",
        "VK_KHR_sampler_mirror_clamp_to_edge",
        "VK_KHR_sampler_ycbcr_conversion",
        "VK_KHR_separate_depth_stencil_layouts",
        "VK_KHR_shader_atomic_int64",
        "VK_KHR_shader_clock",
        "VK_KHR_shader_draw_parameters",
        "VK_KHR_shader_float16_int8",
        "VK_KHR_shader_float_controls",
        "VK_KHR_shader_non_semantic_info",
        "VK_KHR_shader_subgroup_extended_types",
        "VK_KHR_shader_terminate_invocation",
        "VK_KHR_shared_presentable_image",
        "VK_KHR_spirv_1_4",
        "VK_KHR_storage_buffer_storage_class",
        "VK_KHR_surface",
        "VK_KHR_surface_protected_capabilities",
        "VK_KHR_swapchain",
        "VK_KHR_swapchain_mutable_format",
        "VK_KHR_timeline_semaphore",
        "VK_KHR_uniform_buffer_standard_layout",
        "VK_KHR_variable_pointers",
        "VK_KHR_vulkan_memory_model",
        "VK_KHR_wayland_surface",
        "VK_KHR_win32_keyed_mutex",
        "VK_KHR_win32_surface",
        "VK_KHR_xcb_surface",
        "VK_KHR_xlib_surface",
    ];
    let ss = "
    pub use std::ptr::*;
    pub use std::mem::*;
    pub use std::ffi::c_void;
    pub type Result<T> = std::result::Result<T, VkResult>;
    impl std::ops::Try for VkResult {
        type Ok = ();
        type Error = VkResult;
        fn into_result(self) -> std::result::Result<Self::Ok, Self::Error> {
            match self {
                Self::Success => Ok(()),
                err => Err(err),
            }
        }
    
        fn from_ok(v: Self::Ok) -> Self {
            Self::Success
        }
    
        fn from_error(v: Self::Error) -> Self {
            v
        }
    }";
    println!("{}", ss);
    for t in foriegn32 {
        println!("pub type foreign_{} = u32;", t);
    }
    for t in foriegn64 {
        println!("pub type foreign_{} = u64;", t);
    }
    for t in c_voids {
        println!("pub type foreign_{} = c_void;", t);
    }
    for (k, v) in typedefs {
        println!("pub type {} = {};", v, k);
    }
    for ext in ext {
        println!("pub const {0}: *const u8 = \"{0}\\0\".as_ptr();", ext);
    }
    for h in handles {
        println!("#[derive(Default, Debug, Copy, Clone, Eq, PartialEq)]");
        println!("pub struct {}(pub usize);", h.name);
        if !h.cmds.is_empty() {
            h.write()
        }
    }

    for f in fnptrs {
        println!("pub type {} = fn(", f.name);
        for a in f.args.iter() {
            a.write(false);
        }
        let cv = f.ret_cv.replace("pm", "*mut ").replace("pc", "*const ");
        println!(") -> {}{};", cv, f.ret);
    }
}

fn write_enums(enums: &Vec<Enum>, apic: &Enum) {
    println!("pub struct VulkanConstants {{}}");
    println!("impl VulkanConstants {{");
    for c in apic.members.iter() {
        let ty = c.1.tystr();
        println!(
            "\tpub const {}: {} = {}{};",
            &c.0[3..],
            ty,
            c.1.get_val(),
            ty
        );
    }
    println!("}}\n");
    for e in enums {
        println!("#[repr(C)]");
        println!("#[derive(Debug, Copy, Clone, Eq, PartialEq)]");
        if !e.bitmask {
            println!("pub enum {} {{", e.name);
            for (k, v) in e.members.iter() {
                let alias = if let EnumValue::Alias(_) = v {
                    "//"
                } else {
                    ""
                };
                println!("\t{}{} = {},", alias, k, v.get_val());
            }
            println!("}}\n");
        } else {
            println!("pub struct {}(pub VkFlags);", e.name);
            println!("impl {} {{", e.name);
            for (k, v) in e.members.iter() {
                if let EnumValue::Alias(_) = v {
                } else {
                    println!("\tpub const {}: u32 = {};", k, v.get_val());
                }
            }
            println!("}}\n");
        }
    }
}

fn write_structs(structs: &Vec<Struct>, unions: &Vec<Struct>) {
    for st in structs {
        println!("#[repr(C)]");
        println!("#[derive(Debug, Copy, Clone)]");
        println!("pub struct {} {{", st.name);
        for m in st.members.iter() {
            m.write(m.name != "stype");
        }
        println!("}}");
        if !st.retonly {
            println!("impl {} {{", st.name);
            println!("\tpub fn new() -> Self {{\n\t\tSelf {{");
            if !st.stype.is_empty() {
                println!("\t\t\ts_type: {},", st.stype);
            }
            println!("\t\t\t..unsafe {{ zeroed() }}");
            println!("\t\t}}\n\t}}");
            for m in st.members.iter() {
                m.setter();
            }
            println!("}}\n");
        }
    }
    for st in unions {
        println!("#[repr(C)]");
        println!("#[derive(Copy, Clone)]");
        println!("pub union {} {{", st.name);
        for m in st.members.iter() {
            m.write(true);
        }
        println!("}}");

        println!(
            "impl std::fmt::Debug for {} {{
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {{
                Ok(())
            }}
        }}",
            st.name
        );
    }
}

pub fn parse_digit(s: &str) -> Option<i64> {
    if s.starts_with("0x") {
        i64::from_str_radix(&s[2..], 16).ok()
    } else {
        s.parse().ok()
    }
}

fn parse_enums(reg: &XmlNode) -> (Vec<Enum>, Enum) {
    let expr = tokens::ExprParser::new();
    let reg = reg.children();
    let mut enums: Vec<_> = reg
        .iter()
        .filter_map(|n| {
            if n.name == "enums" {
                let bitmask = n
                    .find_attr("type")
                    .map(|v| v == "bitmask")
                    .unwrap_or_default();
                let mut e = Enum {
                    name: n.find_attr("name").unwrap().to_string(),
                    bitmask,
                    ..Default::default()
                };
                n.children().iter().for_each(|n| {
                    if n.name == "enum" {
                        e.extend(n, &expr)
                    }
                });
                Some(e)
            } else {
                None
            }
        })
        .collect();

    for feature in reg.iter().filter(|n| n.name == "feature") {
        for req in feature.children() {
            for c in req.children() {
                if c.name == "enum" {
                    if let Some(v) = c.find_attr("extends") {
                        let e = enums.iter_mut().find(|e| e.name == v).unwrap();
                        e.extend2(c, 0, &expr);
                    }
                }
            }
        }
    }

    for base in reg
        .into_iter()
        .find(|n| n.name == "extensions")
        .unwrap()
        .children()
    {
        let ext_number: i64 = base.find_attr("number").unwrap().parse().unwrap();
        for req in base.children() {
            for c in req.children() {
                if c.name == "enum" {
                    if let Some(v) = c.find_attr("extends") {
                        let e = enums.iter_mut().find(|e| e.name == v).unwrap();
                        e.extend2(c, ext_number, &expr);
                    }
                }
            }
        }
    }

    let apic = enums
        .iter()
        .enumerate()
        .find(|(i, e)| e.name == "API Constants")
        .unwrap()
        .0;
    let apic = enums.remove(apic);
    (enums, apic)
}

fn parse_structs(
    reg: &XmlNode,
) -> (
    Vec<Struct>,
    Vec<Struct>,
    Vec<(String, String)>,
    Vec<Handle>,
    Vec<FnPtr>,
    Vec<FnPtr>,
) {
    let mp = tokens::MemberParser::new();
    let bp = tokens::BaseParser::new();
    let fp = tokens::FuncPtrParser::new();
    let expr = tokens::ExprParser::new();
    let types = find_node(&reg, &|n| n.name == "types").unwrap();
    let mut structs = Vec::<Struct>::new();
    let mut unions = Vec::<Struct>::new();
    let mut typedefs = Vec::<(String, String)>::default();
    let mut handles = vec![];
    let mut fnptrs = vec![];
    let mut statics = vec![];

    for ty in types.children() {
        let c = ty.find_child("type");
        let n = ty.find_child("name");
        let alias = ty.find_attr("alias").is_some();
        let attr = ty.find_attr("category");
        if let Some(a) = ty.find_attr("alias") {
            let n = ty.find_attr("name").unwrap();
            typedefs.push((a.to_string(), n.to_owned()));
        }

        if Some("struct") == attr && !alias {
            let mut st = Struct {
                name: ty.find_attr("name").unwrap().to_string(),
                members: vec![],
                retonly: ty.find_attr("returnedonly").is_some(),
                extends: ty
                    .find_attr("structextends")
                    .map(|s| s.to_owned())
                    .unwrap_or_default(),
                stype: String::new(),
            };
            for c in ty.children() {
                if let Some(stype) = c.find_attr("values") {
                    st.stype = [
                        "VkStructureType::",
                        &stype["VK_STRUCTURE_TYPE_".len()..].to_pascal_case(),
                    ]
                    .concat();
                }
                let mut mem = mp.parse(&c.cpp_type()).unwrap();
                if let Some(len) = c.find_attr("altlen").or(c.find_attr("len")) {
                    if len == "null-terminated" {
                        mem.null_term = true;
                    } else if len.find("null-terminated").is_some() {
                        mem.null_term = true;
                        let len = len.replace(",null-terminated", "");
                        mem.len = expr.parse(&len).unwrap();
                    } else {
                        mem.len = expr.parse(&len).unwrap();
                        //println!("{} {:?}", mem.name, mem.len);
                    }
                    if let Some(s) = mem.len.has_var() {
                        st.members.iter_mut().find(|m| m.name == s).unwrap().is_len = true;
                    }
                }
                mem.ty = mem.ty.replace("FlagBits", "Flags");
                st.members.push(mem);
            }
            structs.push(st);
            continue;
        }
        if Some("union") == attr {
            let mut st = Struct {
                name: ty.find_attr("name").unwrap().to_string(),
                members: vec![],
                ..Default::default()
            };
            for c in ty.children() {
                let mem = mp.parse(&c.cpp_type()).unwrap();
                st.members.push(mem);
            }
            unions.push(st);
            continue;
        }
        if Some("funcpointer") == attr {
            let src = ty.cpp_type();
            fnptrs.push(fp.parse(&src).expect(&src));
        }
        if n.is_some() && (Some("bitmask") == attr || Some("basetype") == attr) {
            let ty = if c.is_some() {
                bp.parse(c.unwrap().get_str()).unwrap()
            } else {
                "usize"
            };
            typedefs.push((ty.to_string(), n.unwrap().get_str().to_string()));
            continue;
        }
        if Some("handle") == attr && !alias {
            let name = ty
                .find_attr("name")
                .unwrap_or_else(|| n.unwrap().get_str())
                .to_string();
            handles.push(Handle {
                name,
                ..Default::default()
            });
            continue;
        }
    }

    //let mut map = <_>::default();
    for cmd in reg.find_child("commands").unwrap().children() {
        match cmd.find_child("proto") {
            Some(c) => {
                //cmd.show("");
                let args = cmd.children().into_iter().filter(|c| c.name == "param");
                let cmd = format!(
                    "{}({});",
                    c.cpp_type(),
                    args.clone()
                        .map(|c| c.cpp_type())
                        .collect::<Vec<_>>()
                        .join(", ")
                );
                let mut cmd: FnPtr = fp.parse(&cmd).unwrap();
                for (arg, node) in cmd.args.iter_mut().zip(args) {
                    //node.get_attr(&mut map);
                    if let Some(len) = node.find_attr("len") {
                        if len == "null-terminated" {
                            arg.null_term = true;
                        } else {
                            arg.len = expr.parse(len).unwrap();
                        }
                    }
                }
                let args: &Vec<StructMember> = unsafe { transmute(&cmd.args) };
                for arg in args.iter() {
                    if let Expr::Accessor(var, _) = &arg.len {
                        cmd.args
                            .iter_mut()
                            .find(|a| &a.name == var)
                            .unwrap()
                            .inner_len = true;
                    } else if let Some(var) = arg.len.has_var() {
                        cmd.args.iter_mut().find(|a| a.name == var).unwrap().is_len = true;
                    }
                }

                let handle = cmd.args.first().unwrap().ty.as_str();
                match handles.iter_mut().find(|c| c.name == handle) {
                    Some(h) => {
                        cmd.args.remove(0);
                        h.cmds.push(cmd);
                    }
                    _ => statics.push(cmd),
                }
            }
            _ => (),
        };
    }
    //println!("{:#?}", map);
    (structs, unions, typedefs, handles, fnptrs, statics)
}

impl Enum {
    pub fn extend(&mut self, n: &XmlNode, parser: &tokens::ExprParser) {
        let name = n.find_attr("name").unwrap().to_string();
        if let Some(m) = self.members.iter().find(|n| n.0 == name) {
            return;
        }

        let c = if let Some(s) = n.find_attr("alias") {
            let e = self.members.iter().find(|e| e.0 == s).unwrap();
            EnumValue::Alias(box e.clone())
        } else if let Some(s) = n.find_attr("bitpos") {
            EnumValue::Bitpos(parse_digit(s).unwrap())
        } else {
            let s = n.find_attr("value").unwrap();
            let val = parse_digit(s).map(|v| Value::i64(v));
            EnumValue::Value(val.unwrap_or_else(|| parser.parse(s).unwrap().eval()))
        };
        self.members.push((name, c));
    }

    pub fn extend2(&mut self, n: &XmlNode, ext: i64, parser: &tokens::ExprParser) {
        let name = n.find_attr("name").unwrap().to_string();
        if let Some(m) = self.members.iter().find(|n| n.0 == name) {
            return;
        }
        let mem = if let Some(n) = n.find_attr("alias") {
            let e = self.members.iter().find(|e| e.0 == n).unwrap();
            EnumValue::Alias(box e.clone())
        } else if self.bitmask {
            EnumValue::Bitpos(n.find_attr("bitpos").unwrap().parse().unwrap())
        } else if let Some(v) = n.find_attr("value") {
            EnumValue::Value(parser.parse(v).unwrap().eval())
        } else {
            let ext = n
                .find_attr("extnumber")
                .map(|n| n.parse().unwrap())
                .unwrap_or(ext)
                - 1;
            let offset: i64 = n.find_attr("offset").unwrap().parse().unwrap();
            let val = 1000000000 + ext * 1000 + offset;
            let val = val * n.find_attr("dir").map(|_| -1).unwrap_or(1);
            EnumValue::Value(Value::i64(val))
        };

        self.members.push((name, mem));
    }

    pub fn rename(&mut self) {
        if self.name == "VkResult" {
            for (n, _) in self.members.iter_mut() {
                *n = n.replace("VK_", "").to_pascal_case();
            }
        } else if let Some(i) = self.name.find("FlagBits") {
            let end = &self.name[i + 8..];
            let front = [&self.name[..i].to_screaming_snake_case(), "_"].concat();
            let back = ["_", &["Bit", end].concat().to_screaming_snake_case()].concat();
            for (n, _) in self.members.iter_mut() {
                *n = [&n.replace(&front, "").replace(&back, ""), end]
                    .concat()
                    .to_pascal_case();

                if n.chars().nth(0).unwrap().is_digit(10) {
                    n.insert(0, '_');
                }
            }
        } else {
            let tags = ["KHR", "NV", "EXT", "AMD", "INTEL", "ANDROID"];
            let mut end = "";
            for t in tags.iter() {
                if self.name.ends_with(t) {
                    end = t;
                    break;
                }
            }
            let front = [
                &self.name[..self.name.len() - end.len()].to_screaming_snake_case(),
                "_",
            ]
            .concat();
            let back = if !end.is_empty() {
                ["_", &end.to_screaming_snake_case()].concat()
            } else {
                String::new()
            };
            self.members.iter_mut().for_each(|(n, e)| {
                *n = n.replace(&front, "").replace(&back, "").to_pascal_case();
                if n.chars().nth(0).unwrap().is_digit(10) {
                    n.insert(0, '_');
                }
            });
        }
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum Value {
    u32(u32),
    u64(u64),
    i64(i64),
    f32(u32),
}

#[macro_use]
extern crate lalrpop_util;
lalrpop_mod!(pub tokens);

pub use std::mem::*;
pub use std::ops::*;

impl Value {
    fn to_f64(self) -> f64 {
        match self {
            Value::f32(v) => unsafe { transmute::<u32, f32>(v) as f64 },
            Value::u64(v) => v as f64,
            Value::u32(v) => v as f64,
            Value::i64(v) => v as f64,
        }
    }

    fn val_str(self) -> &'static str {
        match self {
            Value::f32(v) => "f32",
            Value::u64(v) => "u64",
            Value::u32(v) => "u32",
            Value::i64(v) => "i64",
        }
    }
    fn do_op<T: Mul<Output = T> + Add<Output = T> + Sub<Output = T> + Div<Output = T>>(
        l: T,
        r: T,
        o: char,
    ) -> T {
        match o {
            '+' => l + r,
            '-' => l - r,
            '*' => l * r,
            '/' => l / r,
            _ => unreachable!(),
        }
    }
    pub fn op(self, r: Value, o: char) -> Value {
        let v = Self::do_op(self.to_f64(), r.to_f64(), o);
        match (self, r) {
            (Value::f32(_), _) | (_, Value::f32(_)) => Value::f32(v as _),
            (Value::u64(_), _) | (_, Value::u64(_)) => Value::u64(v as _),
            _ => Value::i64(v as _),
        }
    }

    pub fn unop(self, o: char) -> Value {
        match self {
            Value::u64(v) => Value::u64(v ^ u64::MAX),
            Value::u32(v) => Value::u32(v ^ u32::MAX),
            _ => unreachable!("{} {:?}", o, self),
        }
    }
}

#[derive(Debug, Eq, PartialEq, Hash)]
pub enum Expr {
    Void,
    Val(Value),
    Binop(Box<Expr>, char, Box<Expr>),
    Unop(char, Box<Expr>),
    Var(String),
    Accessor(String, String),
}

impl Default for Expr {
    fn default() -> Self {
        Expr::Void
    }
}

impl Expr {
    pub fn has_var(&self) -> Option<&str> {
        match self {
            Expr::Var(s) => Some(s),
            Expr::Binop(l, _, r) => l.has_var().or(r.has_var()),
            Expr::Unop(_, r) => r.has_var(),
            Expr::Accessor(l, r) => Some(l),
            _ => None,
        }
    }
    pub fn eval_var(&self, var: String) -> String {
        match self {
            Expr::Binop(l, o, r) => {
                format!("({} {} {})", l.eval_var(var.clone()), o, r.eval_var(var))
            }
            Expr::Unop(o, r) => format!("({} {})", o, r.eval_var(var)),
            Expr::Var(_) => var,
            Expr::Val(v) => format!("{}", v.to_f64() as u64),
            _ => unreachable!(),
        }
    }
    pub fn eval(&self) -> Value {
        match self {
            Expr::Val(v) => *v,
            Expr::Binop(l, o, r) => l.eval().op(r.eval(), *o),
            Expr::Unop(o, v) => v.eval().unop(*o),
            _ => unreachable!(),
        }
    }
}

struct test {}

impl std::fmt::Debug for test {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Ok(())
    }
}
