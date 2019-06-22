#[macro_use]
extern crate clap;
#[macro_use]
extern crate failure;
extern crate lexpr;
#[macro_use]
extern crate maplit;
#[macro_use]
extern crate lazy_static;

use std::collections::HashMap;
use std::fs::File;
use std::path::{Path, PathBuf};

use failure::Fallible;
use lexpr::atom::Atom as SexprAtom;
use lexpr::Value as Sexpr;

// An AST expression
#[derive(Debug)]
enum Term {
    Type,
    Prop,
    Var(String),
    App(Box<Term>, Box<Term>),
    Lambda(Abstraction),
    ForAll(Abstraction),
}

#[derive(Debug)]
struct Abstraction {
    binder: String,
    binder_type: Box<Term>,
    body: Box<Term>,
}

// Mapping of variables to their types
type TypeContext = HashMap<String, Term>;

impl Term {
    fn from_symbol(sym: &str) -> Box<Self> {
        Box::new(match sym {
            "Type" => Term::Type,
            "Prop" => Term::Prop,
            s => Term::Var(s.to_string()),
        })
    }

    fn from_sexpr_atom(atom: &SexprAtom) -> Fallible<Box<Self>> {
        match atom {
            SexprAtom::Nil => bail!("nil unrecognized"),
            SexprAtom::Bool(_) => bail!("bool unrecognized"),
            SexprAtom::Number(_) => bail!("numbers unrecognized"),
            SexprAtom::String(_) => bail!("strings unrecognized"),
            SexprAtom::Symbol(s) => Ok(Term::from_symbol(&s)),
            SexprAtom::Keyword(_) => bail!("keyword unrecognized"),
        }
    }

    fn from_sexpr_list(list: &Vec<Sexpr>) -> Fallible<Box<Self>> {
        let first_sexpr = list
            .first()
            .ok_or_else(|| format_err!("empty list unrecognized"))?;

        match first_sexpr.as_symbol() {
            Some("lambda") => Ok(Box::new(Term::Lambda(Abstraction::from_sexpr_list(list)?))),
            Some("forall") => Ok(Box::new(Term::ForAll(Abstraction::from_sexpr_list(list)?))),
            _ => match list.as_slice() {
                [a, b] => Ok(Box::new(Term::App(
                    Term::from_sexpr(a)?,
                    Term::from_sexpr(b)?,
                ))),
                _ => bail!("invalid application"),
            },
        }
    }

    fn from_sexpr(prog: &Sexpr) -> Fallible<Box<Self>> {
        match prog {
            Sexpr::Atom(atom) => Term::from_sexpr_atom(atom),
            Sexpr::List(list) => Term::from_sexpr_list(list),
            Sexpr::ImproperList(_, _) => bail!("improper lists unrecognized"),
        }
    }

    fn eval_with_context(self: &Self, ctx: &TypeContext) -> Box<Self> {
        unimplemented!()
    }

    // Type checking / execution
    fn eval(self: &Self) -> Box<Self> {
        lazy_static! {
            static ref DEFAULT_CONTEXT: TypeContext = hashmap![
                "Type".to_string() => Term::Type,
                "Prop".to_string() => Term::Type,
            ];
        }

        self.eval_with_context(&DEFAULT_CONTEXT)
    }
}

impl Abstraction {
    // Parse list of form (abstraction_type binder binder_type body)
    // TODO: refactor
    fn from_sexpr_list(list: &Vec<Sexpr>) -> Fallible<Self> {
        match list.as_slice() {
            [_, binder, binder_type, body] => Ok(Self {
                binder: binder
                    .as_symbol()
                    .ok_or_else(|| format_err!("binder in lambda is not a symbol"))?
                    .to_string(),
                binder_type: Term::from_sexpr(binder_type)?,
                body: Term::from_sexpr(body)?,
            }),
            _ => bail!("abstraction format error"),
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
    let sexpr = lexpr::from_reader(file)?;
    let prog = Term::from_sexpr(&sexpr)?;
    let out = prog.eval();

    println!("{:?}", prog);
    println!("{:?}", out);

    Ok(())
}

// Wrapper of `try_main()` to handle propagated errors
fn main() {
    if let Err(err) = try_main() {
        eprintln!("{}: error: {}", env!("CARGO_PKG_NAME"), err);
        std::process::exit(1);
    }
}
