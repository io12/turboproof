#[macro_use]
extern crate clap;
#[macro_use]
extern crate failure;
extern crate lexpr;

use std::fs::File;
use std::path::{Path, PathBuf};

use failure::Fallible;
use lexpr::atom::Atom as SexprAtom;
use lexpr::Value as Sexpr;

// An AST expression
enum Expr {
    Type,
    Prop,
    Var(String),
    App(Box<Expr>, Box<Expr>),
    Lambda(Abstraction),
    ForAll(Abstraction),
}

struct Abstraction {
    binder: String,
    binder_type: Box<Expr>,
    body: Box<Expr>,
}

impl Expr {
    fn make_var(name: &str) -> Self {
        Expr::Var(name.to_string())
    }

    fn from_sexpr_atom(atom: SexprAtom) -> Fallible<Self> {
        match atom {
            SexprAtom::Nil => Ok(Expr::make_var("nil")),
            SexprAtom::Bool(b) => Ok(Expr::Var(b.to_string())),
            SexprAtom::Number(_) => bail!("numbers unsupported"),
            SexprAtom::String(_) => bail!("strings unsupported"),
            SexprAtom::Symbol(s) => Ok(Expr::make_var(&s)),
            SexprAtom::Keyword(s) => Ok(Expr::make_var(&s)),
        }
    }

    fn from_sexpr_list(list: Vec<Sexpr>) -> Fallible<Self> {
        match list {
            []
        }
    }

    fn from_sexpr(prog: Sexpr) -> Fallible<Self> {
        match prog {
            Sexpr::Atom(atom) => Expr::from_sexpr_atom(atom),
            Sexpr::List(list) => Expr::from_sexpr_list(list),
            Sexpr::ImproperList(_, _) => bail!("improper lists unsupported"),
        }
    }
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
