extern crate lalrpop;
use cc::*;
fn main() {
    lalrpop::process_root().unwrap();
}
