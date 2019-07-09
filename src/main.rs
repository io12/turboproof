#[macro_use]
extern crate clap;
#[macro_use]
extern crate failure;
extern crate im;
extern crate lexpr;

use std::cmp::Ordering;
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
    Print(Term),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum Term {
    Type,
    Var(Var),
    App(Box<Term>, Box<Term>),
    Lambda(Abstraction),
    ForAll(Abstraction),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum Var {
    Global(String), // Globally-defined name
    Local(usize),   // De Bruijn index
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct Abstraction {
    binder_type: Box<Term>,
    body: Box<Term>,
}

#[derive(Debug, Clone)]
struct Context {
    // Mapping of global names to values
    global_vars: OrdMap<String, Term>,
    // Mapping of local bindings (De Bruijn indices) to their types.
    // This vector is indexed as `vec[De Bruijn index - 1]`. Entering
    // the scope of an abstraction during type checking prepends the
    // abstraction's binder type to this.
    local_binding_types: Vec<Term>,
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
    fn eval(&self) -> Fallible<()> {
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

    // TODO: remove this boilerplate somehow
    fn print_from_sexpr_list(list: &Vec<Sexpr>) -> Fallible<Self> {
        match list.as_slice() {
            [_, term] => {
                let term = Term::from_sexpr(term)?;
                Ok(Directive::Print(term))
            }
            _ => bail!("print directive needs 1 parameter"),
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
            "Print" => Directive::print_from_sexpr_list(list),
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

        println!("{} defined", name);
        Ok(ctx.add_global_var(name, val))
    }

    fn eval_check(term: &Term, ctx: &Context) -> Fallible<()> {
        println!("type: {:#?}", term.get_type(ctx)?);
        Ok(())
    }

    fn eval_print(term: &Term, ctx: &Context) -> Fallible<()> {
        println!("term: {:#?}", term.beta_reduce(ctx)?);
        Ok(())
    }

    fn eval(&self, ctx: &Context) -> Fallible<Context> {
        match self {
            Directive::Define(name, val) => Ok(ctx.add_global_var(name, val)),
            Directive::DefineWithType(name, val, typ) => {
                Directive::eval_define_with_type(name, val, typ, ctx)
            }
            Directive::Check(term) => {
                Directive::eval_check(term, ctx)?;
                Ok(ctx.to_owned())
            }
            Directive::Print(term) => {
                Directive::eval_print(term, ctx)?;
                Ok(ctx.to_owned())
            }
        }
    }
}

impl Term {
    fn from_symbol(sym: &str, var_stack: &Vec<String>) -> Self {
        match sym {
            "Type" => Term::Type,
            sym => Term::Var(Var::from_symbol(sym, var_stack)),
        }
    }

    fn from_sexpr_atom(atom: &SexprAtom, var_stack: &Vec<String>) -> Fallible<Self> {
        match atom {
            SexprAtom::Nil => bail!("nil unrecognized"),
            SexprAtom::Bool(_) => bail!("bool unrecognized"),
            SexprAtom::Number(_) => bail!("numbers unrecognized"),
            SexprAtom::String(_) => bail!("strings unrecognized"),
            SexprAtom::Symbol(s) => Ok(Term::from_symbol(&s, var_stack)),
            SexprAtom::Keyword(_) => bail!("keyword unrecognized"),
        }
    }

    fn app_from_sexpr_list(list: &[Sexpr], var_stack: &Vec<String>) -> Fallible<Term> {
        let list = list
            .iter()
            .map(|exp| Term::from_sexpr_vstk(exp, var_stack))
            .map(|res_term| res_term.map(|term| Box::new(term)))
            .collect::<Fallible<Vec<_>>>()?;

        match list.split_first() {
            Some((head, tail)) => tail
                .iter()
                .try_fold(head.to_owned(), |a, b| {
                    let b = b.to_owned();
                    let term = Term::App(a, b);

                    Ok(Box::new(term))
                })
                .map(|term| *term),
            None => bail!("empty list unrecognized"),
        }
    }

    fn from_sexpr_list(list: &Vec<Sexpr>, var_stack: &Vec<String>) -> Fallible<Self> {
        let first_sexpr = list
            .first()
            .ok_or_else(|| format_err!("empty list unrecognized"))?;

        match first_sexpr.as_symbol() {
            Some("lambda") => Ok(Term::Lambda(Abstraction::from_sexpr_list(list, var_stack)?)),
            Some("forall") => Ok(Term::ForAll(Abstraction::from_sexpr_list(list, var_stack)?)),
            _ => Term::app_from_sexpr_list(list, var_stack),
        }
    }

    fn from_sexpr_vstk(prog: &Sexpr, var_stack: &Vec<String>) -> Fallible<Self> {
        match prog {
            Sexpr::Atom(atom) => Term::from_sexpr_atom(atom, var_stack),
            Sexpr::List(list) => Term::from_sexpr_list(list, var_stack),
            Sexpr::ImproperList(_, _) => bail!("improper lists unrecognized"),
        }
    }

    fn from_sexpr(sexpr: &Sexpr) -> Fallible<Self> {
        Term::from_sexpr_vstk(sexpr, &Vec::new())
    }

    fn get_app_type(m: &Term, n: &Term, ctx: &Context) -> Fallible<Self> {
        if let (Ok(Term::ForAll(abs)), Ok(arg_type)) = (m.get_type(ctx), n.get_type(ctx)) {
            if *abs.binder_type == arg_type {
                Ok(abs.do_app(n))
            } else {
                Err(format_err!("invalid application"))
            }
        } else {
            Err(format_err!("invalid application"))
        }
    }

    fn get_lambda_type(abs: &Abstraction, ctx: &Context) -> Fallible<Self> {
        let Abstraction { binder_type, body } = abs;

        let ctx = ctx.enter_abstraction(binder_type);

        let body_type = body.get_type(&ctx)?;

        Ok(Term::ForAll(Abstraction {
            binder_type: binder_type.to_owned(),
            body: Box::new(body_type),
        }))
    }

    fn get_var_type(var: &Var, ctx: &Context) -> Fallible<Self> {
        match var {
            Var::Global(name) => ctx
                .get_global_var(name)
                .ok_or_else(|| format_err!("variable '{}' not in scope", name))
                .and_then(|term| term.get_type(ctx)),
            &Var::Local(n) => Ok(ctx.get_local_binding_type(n).to_owned()),
        }
    }

    // Type checking
    fn get_type(&self, ctx: &Context) -> Fallible<Self> {
        match self {
            Term::Type => bail!("Tried to get type of `Type`"),
            Term::Var(var) => Term::get_var_type(var, ctx),
            Term::App(m, n) => Term::get_app_type(m, n, ctx),
            Term::Lambda(abs) => Term::get_lambda_type(abs, ctx),
            // TODO: Does this break soundness if the `ForAll` contains `Type`?
            Term::ForAll(_) => Ok(Term::Type),
        }?
        .beta_reduce(ctx)
    }

    fn beta_reduce_step_var(var: &Var, ctx: &Context) -> Fallible<Self> {
        match var {
            Var::Global(name) => ctx
                .get_global_var(name)
                .map(|term| term.to_owned())
                .ok_or_else(|| {
                    format_err!("variable '{}' not in scope during beta-reduction", name)
                }),
            Var::Local(_) => Ok(Term::Var(var.to_owned())),
        }
    }

    fn beta_reduce_step_app(m: &Term, n: &Term, ctx: &Context) -> Fallible<Self> {
        if let Some(abs) = m.get_abstraction() {
            abs.do_app(&n).beta_reduce_step(ctx)
        } else {
            let (m, n) = (m.beta_reduce_step(ctx)?, n.beta_reduce_step(ctx)?);
            let (m, n) = (Box::new(m), Box::new(n));
            Ok(Term::App(m, n))
        }
    }

    // Single beta-reduction step, representing one step of term
    // evaluation
    fn beta_reduce_step(&self, ctx: &Context) -> Fallible<Self> {
        match self {
            Term::Type => Ok(self.to_owned()),
            Term::Var(var) => Term::beta_reduce_step_var(var, ctx),
            Term::App(m, n) => Term::beta_reduce_step_app(m, n, ctx),
            Term::Lambda(abs) => Ok(Term::Lambda(abs.beta_reduce_step(ctx)?)),
            Term::ForAll(abs) => Ok(Term::ForAll(abs.beta_reduce_step(ctx)?)),
        }
    }

    fn get_abstraction(&self) -> Option<&Abstraction> {
        match self {
            Term::Lambda(abs) | Term::ForAll(abs) => Some(abs),
            _ => None,
        }
    }

    fn is_abstraction(&self) -> bool {
        self.get_abstraction().is_some()
    }

    fn is_app_normal(m: &Term, n: &Term, ctx: &Context) -> bool {
        !m.is_abstraction() && m.is_normal(ctx) && n.is_normal(ctx)
    }

    fn is_normal(&self, ctx: &Context) -> bool {
        match self {
            Term::Type | Term::Var(Var::Local(_)) => true,
            Term::Var(Var::Global(name)) => ctx.get_global_var(name).is_none(),
            Term::App(m, n) => Term::is_app_normal(m, n, ctx),
            Term::Lambda(abs) | Term::ForAll(abs) => abs.body.is_normal(ctx),
        }
    }

    // Full beta-reduction of terms to their normal form
    fn beta_reduce(&self, ctx: &Context) -> Fallible<Self> {
        if self.is_normal(ctx) {
            Ok(self.to_owned())
        } else {
            self.beta_reduce_step(ctx)?.beta_reduce(ctx)
        }
    }

    fn do_app_depth(&self, arg: &Term, depth: usize) -> Self {
        match self {
            Term::Type | Term::Var(Var::Global(_)) => self.to_owned(),
            &Term::Var(Var::Local(n)) => match n.cmp(&depth) {
                Ordering::Less => self.to_owned(),
                Ordering::Greater => Term::Var(Var::Local(n - 1)),
                Ordering::Equal => arg.to_owned(),
            },
            Term::App(m, n) => {
                let (m, n) = (m.do_app_depth(arg, depth), n.do_app_depth(arg, depth));
                let (m, n) = (Box::new(m), Box::new(n));
                Term::App(m, n)
            }
            Term::Lambda(abs) => Term::Lambda(abs.do_app_depth_helper(arg, depth)),
            Term::ForAll(abs) => Term::ForAll(abs.do_app_depth_helper(arg, depth)),
        }
    }
}

impl Var {
    fn from_symbol(name: &str, var_stack: &Vec<String>) -> Self {
        match var_stack.iter().rev().position(|var| var == name) {
            Some(ind) => Var::Local(ind + 1),
            None => Var::Global(name.to_string()),
        }
    }
}

impl Abstraction {
    // Parse list of form (abstraction_type binder binder_type body)
    // TODO: refactor
    fn from_sexpr_list(list: &Vec<Sexpr>, var_stack: &Vec<String>) -> Fallible<Self> {
        match list.as_slice() {
            [_, binder, binder_type, body] => {
                let binder = binder
                    .as_symbol()
                    .ok_or_else(|| format_err!("binder in lambda is not a symbol"))?
                    .to_string();

                let binder_type = Term::from_sexpr_vstk(binder_type, var_stack)?;
                let binder_type = Box::new(binder_type);

                let mut var_stack = var_stack.to_owned();
                var_stack.push(binder);

                let body = Term::from_sexpr_vstk(body, &var_stack)?;
                let body = Box::new(body);

                Ok(Self { binder_type, body })
            }
            _ => bail!("abstraction format error"),
        }
    }

    fn beta_reduce_step(&self, ctx: &Context) -> Fallible<Self> {
        let Self { binder_type, body } = self.to_owned();

        let ctx = ctx.enter_abstraction(&*binder_type);

        let body = Box::new(body.beta_reduce_step(&ctx)?);

        Ok(Self { binder_type, body })
    }

    fn do_app(&self, arg: &Term) -> Term {
        self.body.do_app_depth(arg, 1)
    }

    fn do_app_depth_helper(&self, arg: &Term, depth: usize) -> Self {
        let binder_type = self.binder_type.do_app_depth(arg, depth);
        let binder_type = Box::new(binder_type);

        let body = self.body.do_app_depth(arg, depth + 1);
        let body = Box::new(body);

        Self { binder_type, body }
    }
}

impl Context {
    fn new() -> Self {
        Self {
            global_vars: OrdMap::new(),
            local_binding_types: Vec::new(),
        }
    }

    fn add_global_var(&self, name: &str, val: &Term) -> Self {
        let Self {
            global_vars,
            local_binding_types,
        } = self.to_owned();

        let global_vars = global_vars.update(name.to_string(), val.to_owned());

        Self {
            global_vars,
            local_binding_types,
        }
    }

    fn enter_abstraction(&self, binding_type: &Term) -> Self {
        let Self {
            global_vars,
            mut local_binding_types,
        } = self.to_owned();

        local_binding_types.push(binding_type.to_owned());

        Self {
            global_vars,
            local_binding_types,
        }
    }

    fn get_global_var(&self, name: &str) -> Option<&Term> {
        self.global_vars.get(name)
    }

    fn get_local_binding_type(&self, n: usize) -> &Term {
        // An out of bounds index here means an error in the code, so
        // panicking instead of a meaningful error is okay
        self.local_binding_types
            .iter()
            .rev()
            .nth(n - 1)
            .expect("couldn't get local binding type")
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
