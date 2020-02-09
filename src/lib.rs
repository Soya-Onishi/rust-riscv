mod core;
mod util;

use std::env;

fn main() {
    let args: Vec<String> = env::args().collect();

    for filename in args[1..].iter() {
        println!("run: {}", &filename);
        let mut core = core::Core::new(0, true);
        core.load_and_run(filename.clone());
        println!();
    }
}
