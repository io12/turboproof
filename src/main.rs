#[macro_use]
extern crate clap;
#[macro_use]
extern crate failure;
extern crate im;
extern crate lexpr;

use std::fs::File;
use std::path::{Path, PathBuf};

use failure::Fallible;
use lexpr::atom::Atom as SexprAtom;
use lexpr::Value as Sexpr;

// An AST expression
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum Term {
    Type,
    Prop,
    Var(String),
    App(Box<Term>, Box<Term>),
    Lambda(Abstraction),
    ForAll(Abstraction),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct Abstraction {
    binder: String,
    binder_type: Box<Term>,
    body: Box<Term>,
}

// Mapping of variables to their types
type TypeContext = im::ordmap::OrdMap<Term, Term>;

impl Term {
    fn from_symbol(sym: &str) -> Self {
        match sym {
            "Type" => Term::Type,
            "Prop" => Term::Prop,
            s => Term::Var(s.to_string()),
        }
    }

    fn from_sexpr_atom(atom: &SexprAtom) -> Fallible<Self> {
        match atom {
            SexprAtom::Nil => bail!("nil unrecognized"),
            SexprAtom::Bool(_) => bail!("bool unrecognized"),
            SexprAtom::Number(_) => bail!("numbers unrecognized"),
            SexprAtom::String(_) => bail!("strings unrecognized"),
            SexprAtom::Symbol(s) => Ok(Term::from_symbol(&s)),
            SexprAtom::Keyword(_) => bail!("keyword unrecognized"),
        }
    }

    fn from_sexpr_list(list: &Vec<Sexpr>) -> Fallible<Self> {
        let first_sexpr = list
            .first()
            .ok_or_else(|| format_err!("empty list unrecognized"))?;

        match first_sexpr.as_symbol() {
            Some("lambda") => Ok(Term::Lambda(Abstraction::from_sexpr_list(list)?)),
            Some("forall") => Ok(Term::ForAll(Abstraction::from_sexpr_list(list)?)),
            _ => match list.as_slice() {
                [a, b] => Ok(Term::App(
                    Box::new(Term::from_sexpr(a)?),
                    Box::new(Term::from_sexpr(b)?),
                )),
                _ => bail!("invalid application"),
            },
        }
    }

    fn from_sexpr(prog: &Sexpr) -> Fallible<Self> {
        match prog {
            Sexpr::Atom(atom) => Term::from_sexpr_atom(atom),
            Sexpr::List(list) => Term::from_sexpr_list(list),
            Sexpr::ImproperList(_, _) => bail!("improper lists unrecognized"),
        }
    }

    fn subst(self: &Self, var: &str, val: &Term) -> Self {
        match self {
            Term::Type | Term::Prop => self.to_owned(),
            Term::Var(name) => if name == var { val } else { self }.to_owned(),
            Term::App(m, n) => Term::App(Box::new(m.subst(var, val)), Box::new(n.subst(var, val))),
            Term::Lambda(abs) => Term::Lambda(abs.subst(var, val)),
            Term::ForAll(abs) => Term::ForAll(abs.subst(var, val)),
        }
    }

    fn get_app_type(m: &Term, n: &Term, ctx: &TypeContext) -> Fallible<Self> {
        if let (
            Some(Term::ForAll(Abstraction {
                binder: x,
                binder_type: a_0,
                body: b,
            })),
            Some(a_1),
        ) = (ctx.get(m), ctx.get(n))
        {
            if **a_0 == *a_1 {
                Ok(b.subst(x, n))
            } else {
                Err(format_err!("invalid application"))
            }
        } else {
            Err(format_err!("invalid application"))
        }
    }

    fn is_type_or_prop(self: &Self) -> bool {
        match self {
            Term::Type | Term::Prop => true,
            _ => false,
        }
    }

    fn get_lambda_type(abs: &Abstraction, ctx: &TypeContext) -> Fallible<Self> {
        let Abstraction {
            binder,
            binder_type,
            body,
        } = abs.clone();

        let ctx = ctx.update(Term::Var(binder.clone()), *binder_type.clone());

        let body_type = body.get_type_with_context(&ctx)?;
        let body_type_type = body_type.get_type_with_context(&ctx)?;

        ensure!(
            body_type_type.is_type_or_prop(),
            "failed to type check lambda"
        );

        Ok(Term::ForAll(Abstraction {
            binder,
            binder_type,
            body: Box::new(body_type),
        }))
    }

    // Type checking with a custom context
    fn get_type_with_context(self: &Self, ctx: &TypeContext) -> Fallible<Self> {
        match self {
            Term::Type | Term::Prop => Ok(self.to_owned()),
            Term::Var(name) => ctx
                .get(self)
                .map(|term| term.to_owned())
                .ok_or_else(|| format_err!("could not find binding '{}' in scope", name)),
            Term::App(m, n) => Term::get_app_type(m, n, ctx),
            Term::Lambda(abs) => Term::get_lambda_type(abs, ctx),
            Term::ForAll(_) => Ok(Term::Prop),
        }
    }

    // Type checking
    fn get_type(self: &Self) -> Fallible<Self> {
        let ctx = TypeContext::new();
        self.get_type_with_context(&ctx)
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
                binder_type: Box::new(Term::from_sexpr(binder_type)?),
                body: Box::new(Term::from_sexpr(body)?),
            }),
            _ => bail!("abstraction format error"),
        }
    }

    fn subst(self: &Self, var: &str, val: &Term) -> Self {
        if self.binder == var {
            self.to_owned()
        } else {
            let Self {
                binder,
                binder_type,
                body,
            } = self.to_owned();
            Self {
                binder,
                binder_type,
                body: Box::new(body.subst(var, val)),
            }
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
    let typ = prog.get_type()?;

    println!("program: {:?}", prog);
    println!("type: {:?}", typ);

    Ok(())
}

// Wrapper of `try_main()` to handle propagated errors
fn main() {
    if let Err(err) = try_main() {
        eprintln!("{}: error: {}", env!("CARGO_PKG_NAME"), err);
        std::process::exit(1);
    }
}
