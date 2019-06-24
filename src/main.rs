#[macro_use]
extern crate clap;
#[macro_use]
extern crate failure;
extern crate im;
extern crate lexpr;

use std::path::{Path, PathBuf};

use failure::Fallible;
use im::ordmap::OrdMap;
use lexpr::atom::Atom as SexprAtom;
use lexpr::Value as Sexpr;

#[derive(Debug)]
struct Ast {
    directives: Vec<Directive>,
}

#[derive(Debug)]
enum Directive {
    Define(String, Term),
    DefineWithType(String, Term, Term),
    Check(Term),
}

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

#[derive(Debug, Clone)]
struct Context {
    // Mapping of variable names to values
    vars: OrdMap<String, Term>,
    // Mapping of terms to their types
    types: OrdMap<Term, Term>,
}

impl Ast {
    fn from_sexprs(sexprs: &Vec<Sexpr>) -> Fallible<Self> {
        Ok(Self {
            directives: sexprs
                .iter()
                .map(|exp| Directive::from_sexpr(exp))
                .collect::<Fallible<Vec<_>>>()?,
        })
    }

    // TODO: make this clearer
    fn eval(self: &Self) -> Fallible<()> {
        self.directives
            .iter()
            .fold(Ok(Context::new()), |ctx, direct| match ctx {
                Ok(ctx) => direct.eval(&ctx),
                err => err,
            })
            .map(|_| ())
    }
}

impl Directive {
    // TODO: remove this boilerplate somehow
    // (Define name val [type])
    fn define_from_sexpr_list(list: &Vec<Sexpr>) -> Fallible<Self> {
        ensure!(
            list.len() == 3 || list.len() == 4,
            "define directive has incorrect amount of parameters"
        );

        let name = list
            .get(1)
            .ok_or_else(|| format_err!("define directive has no name"))?
            .as_symbol()
            .ok_or_else(|| format_err!("name in define directive is not a symbol"))?
            .to_string();

        let val = list
            .get(2)
            .ok_or_else(|| format_err!("define directive has no value"))
            .and_then(|val| Term::from_sexpr(val))?;

        let maybe_type = list.get(3).and_then(|typ| Term::from_sexpr(typ).ok());

        Ok(match maybe_type {
            Some(typ) => Directive::DefineWithType(name, val, typ),
            None => Directive::Define(name, val),
        })
    }

    // TODO: remove this boilerplate somehow
    fn check_from_sexpr_list(list: &Vec<Sexpr>) -> Fallible<Self> {
        match list.as_slice() {
            [_, term] => {
                let term = Term::from_sexpr(term)?;
                Ok(Directive::Check(term))
            }
            _ => bail!("check directive needs 1 parameter"),
        }
    }

    fn from_sexpr_list(list: &Vec<Sexpr>) -> Fallible<Self> {
        let first_sym = list
            .first()
            .ok_or_else(|| format_err!("directive is an empty list"))?
            .as_symbol()
            .ok_or_else(|| format_err!("first item of directive is not a symbol"))?;

        match first_sym {
            "Define" => Directive::define_from_sexpr_list(list),
            "Check" => Directive::check_from_sexpr_list(list),
            _ => bail!("unknown directive '{}'", first_sym),
        }
    }

    fn from_sexpr(sexpr: &Sexpr) -> Fallible<Self> {
        match sexpr {
            Sexpr::List(list) => Directive::from_sexpr_list(list),
            _ => bail!("expected directive but did not get list"),
        }
    }

    fn eval_define_with_type(
        name: &str,
        val: &Term,
        typ: &Term,
        ctx: &Context,
    ) -> Fallible<Context> {
        let left = val.get_type(ctx)?.beta_reduce(ctx)?;
        let right = typ.beta_reduce(ctx)?;
        if left != right {
            bail!(
                "type disagreement\n  left: {:#?}\n  right: {:#?}",
                left,
                right
            );
        }

        Ok(ctx.add_var(name, val))
    }

    fn eval_check(term: &Term, ctx: &Context) -> Fallible<()> {
        println!("type: {:#?}", term.get_type(ctx)?);
        Ok(())
    }

    fn eval(self: &Self, ctx: &Context) -> Fallible<Context> {
        match self {
            Directive::Define(name, val) => Ok(ctx.add_var(name, val)),
            Directive::DefineWithType(name, val, typ) => {
                Directive::eval_define_with_type(name, val, typ, ctx)
            }
            Directive::Check(term) => {
                Directive::eval_check(term, ctx)?;
                Ok(ctx.to_owned())
            }
        }
    }
}

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

    fn get_app_type(m: &Term, n: &Term, ctx: &Context) -> Fallible<Self> {
        if let (
            Some(Term::ForAll(Abstraction {
                binder: x,
                binder_type: a_0,
                body: b,
            })),
            Some(a_1),
        ) = (ctx.get_type(m), ctx.get_type(n))
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

    fn get_lambda_type(abs: &Abstraction, ctx: &Context) -> Fallible<Self> {
        let Abstraction {
            binder,
            binder_type,
            body,
        } = abs.clone();

        let ctx = ctx.add_type(&Term::Var(binder.clone()), &*binder_type);

        let body_type = body.get_type(&ctx)?;

        Ok(Term::ForAll(Abstraction {
            binder,
            binder_type,
            body: Box::new(body_type),
        }))
    }

    fn get_var_type(name: &str, ctx: &Context) -> Fallible<Self> {
        let maybe_type = ctx.get_type(&Term::Var(name.to_string()));

        match maybe_type {
            Some(typ) => Ok(typ.to_owned()),
            None => ctx
                .get_var(name)
                .ok_or_else(|| format_err!("could not find binding '{}' in scope", name))?
                .get_type(ctx),
        }
    }

    // Type checking
    fn get_type(self: &Self, ctx: &Context) -> Fallible<Self> {
        match self {
            Term::Type | Term::Prop => Ok(Term::Type),
            Term::Var(name) => Term::get_var_type(name, ctx),
            Term::App(m, n) => Term::get_app_type(m, n, ctx),
            Term::Lambda(abs) => Term::get_lambda_type(abs, ctx),
            Term::ForAll(_) => Ok(Term::Prop),
        }?
        .beta_reduce(ctx)
    }

    fn beta_reduce_step_var(name: &str, ctx: &Context) -> Self {
        ctx.get_var(name)
            .map(|term| term.to_owned())
            .unwrap_or(Term::Var(name.to_string()))
    }

    fn beta_reduce_step_app(m: &Term, n: &Term, ctx: &Context) -> Fallible<Self> {
        if let Some(Abstraction {
            binder,
            binder_type,
            body,
        }) = m.get_abstraction()
        {
            body.subst(&binder, &n).beta_reduce_step(ctx)
        } else {
            let (m, n) = (m.to_owned(), n.to_owned());
            let (m, n) = (Box::new(m), Box::new(n));
            Ok(Term::App(m, n))
        }
    }

    // Single beta-reduction step, representing one step of term
    // evaluation
    fn beta_reduce_step(self: &Self, ctx: &Context) -> Fallible<Self> {
        match self {
            Term::Type | Term::Prop => Ok(self.to_owned()),
            Term::Var(name) => Ok(Term::beta_reduce_step_var(name, ctx)),
            Term::App(m, n) => Term::beta_reduce_step_app(m, n, ctx),
            Term::Lambda(abs) => Ok(Term::Lambda(abs.beta_reduce_step(ctx)?)),
            Term::ForAll(abs) => Ok(Term::ForAll(abs.beta_reduce_step(ctx)?)),
        }
    }

    fn get_abstraction(self: &Self) -> Option<&Abstraction> {
        match self {
            Term::Lambda(abs) | Term::ForAll(abs) => Some(abs),
            _ => None,
        }
    }

    fn is_abstraction(self: &Self) -> bool {
        self.get_abstraction().is_some()
    }

    fn is_app_normal(m: &Term, n: &Term, ctx: &Context) -> bool {
        !m.is_abstraction() && m.is_normal(ctx) && n.is_normal(ctx)
    }

    fn is_normal(self: &Self, ctx: &Context) -> bool {
        let b = match self {
            Term::Type | Term::Prop => true,
            Term::Var(name) => ctx.get_var(name).is_none(),
            Term::App(m, n) => Term::is_app_normal(m, n, ctx),
            Term::Lambda(abs) | Term::ForAll(abs) => abs.body.is_normal(ctx),
        };
        //println!("normal {}: {:#?}", b, self);
        b
    }

    // Full beta-reduction of terms to their normal form
    fn beta_reduce(self: &Self, ctx: &Context) -> Fallible<Self> {
        println!("beta-reduce: {:#?}", self);
        if self.is_normal(ctx) {
            Ok(self.to_owned())
        } else {
            self.beta_reduce_step(ctx)?.beta_reduce(ctx)
        }
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

    fn beta_reduce_step(self: &Self, ctx: &Context) -> Fallible<Self> {
        let Self {
            binder,
            binder_type,
            body,
        } = self.to_owned();

        Ok(Self {
            binder,
            binder_type,
            body: Box::new(body.beta_reduce_step(ctx)?),
        })
    }
}

impl Context {
    fn new() -> Self {
        Self {
            vars: OrdMap::new(),
            types: OrdMap::new(),
        }
    }

    fn add_var(self: &Self, name: &str, val: &Term) -> Self {
        let Self { vars, types } = self.to_owned();
        Self {
            vars: vars.update(name.to_string(), val.to_owned()),
            types,
        }
    }

    fn add_type(self: &Self, val: &Term, typ: &Term) -> Self {
        let Self { vars, types } = self.to_owned();
        Self {
            vars,
            types: types.update(val.to_owned(), typ.to_owned()),
        }
    }

    fn get_var(self: &Self, name: &str) -> Option<&Term> {
        self.vars.get(name)
    }

    fn get_type(self: &Self, val: &Term) -> Option<&Term> {
        self.types.get(val)
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

fn unwrap_sexpr_list(sexpr: Sexpr) -> Vec<Sexpr> {
    match sexpr {
        Sexpr::List(sexprs) => sexprs,
        _ => panic!("expected sexpr list"),
    }
}

fn try_main() -> Fallible<()> {
    let path = get_input_path();

    let code = std::fs::read_to_string(path)?;

    // Surround code with parens so there is a list of directives at
    // the top level
    let code = format!("( {} )", code);

    let sexprs = lexpr::from_str(&code)?;
    let sexprs = unwrap_sexpr_list(sexprs);

    let prog = Ast::from_sexprs(&sexprs)?;

    prog.eval()
}

// Wrapper of `try_main()` to handle propagated errors
fn main() {
    if let Err(err) = try_main() {
        eprintln!("{}: error: {}", env!("CARGO_PKG_NAME"), err);
        std::process::exit(1);
    }
}
