mod core;
mod util;

fn main() {
    let mut core = core::Core::new(0);
    core.load_and_run("rv32ui-p-lw".to_string());
}
