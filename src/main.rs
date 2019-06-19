#[macro_use]
extern crate clap;
extern crate failure;
extern crate lexpr;

use std::path::{Path, PathBuf};

use failure::Fallible;

fn parse_args() -> clap::ArgMatches<'static> {
    app_from_crate!()
        .args_from_usage("<INPUT> 'The input file to evaluate'")
        .get_matches()
}

fn get_input_file() -> PathBuf {
    let args = parse_args();
    let path = args.value_of_os("INPUT").expect("INPUT unspecified");
    Path::new(path).to_path_buf()
}

fn try_main() -> Fallible<()> {
    let inp = get_input_file();
    println!("Got input file: {:?}", inp);

    Ok(())
}

fn main() {
    if let Err(err) = try_main() {
        eprintln!("{}: error: {}", env!("CARGO_PKG_NAME"), err);
        std::process::exit(1);
    }
}
