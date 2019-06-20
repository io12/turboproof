#[macro_use]
extern crate clap;
extern crate failure;
extern crate lexpr;

use std::fs::File;
use std::path::{Path, PathBuf};

use failure::Fallible;

// An AST expression
enum Expr {
    Var(String),
    App(Box<Expr>, Box<Expr>),
    Lambda(String, Box<Expr>),
    Inductive(Inductive),
}

// Inductive type definition
struct Inductive {
    name: String,
    params: Vec<Expr>,
    type_: Box<Expr>,
    variants: Vec<InductiveVariant>,
}

// Variant (branch) in an inductive type definition
struct InductiveVariant {
    name: String,
    type_: Box<Expr>,
}

// Use clap crate to parse args
fn parse_args() -> clap::ArgMatches<'static> {
    app_from_crate!()
        .args_from_usage("<INPUT> 'The input file to evaluate'")
        .get_matches()
}

// Get path of the input file to evaluate by parsing the program args
fn get_input_path() -> PathBuf {
    let args = parse_args();
    let path = args.value_of_os("INPUT").expect("INPUT unspecified");
    Path::new(path).to_path_buf()
}

fn try_main() -> Fallible<()> {
    let path = get_input_path();
    let file = File::open(path)?;
    let prog = lexpr::from_reader(file)?;

    println!("{:?}", prog);

    Ok(())
}

// Wrapper of `try_main()` to handle propagated errors
fn main() {
    if let Err(err) = try_main() {
        eprintln!("{}: error: {}", env!("CARGO_PKG_NAME"), err);
        std::process::exit(1);
    }
}
