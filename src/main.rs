#[macro_use]
extern crate clap;
#[macro_use]
extern crate failure;
extern crate im;
extern crate lexpr;

use std::cmp::Ordering;
use std::fmt;
use std::path::{Path, PathBuf};

use failure::Fallible;
use im::ordmap::OrdMap;
use lexpr::atom::Atom as SexprAtom;
use lexpr::Value as Sexpr;

/// Abstract syntax tree of a TurboProof program
struct Ast {
    /// List of directives
    directives: Vec<Directive>,
}

/// A global name definition
struct DefineDirective {
    /// Name to define
    name: String,
    /// Value and its type
    type_val: TypeVal,
}

/// Binding of a name to a type
struct Binding {
    name: String,
    typ: Term,
}

/// Inductive data type definition
struct DataDirective {
    /// Name of the type constructor
    name: String,
    /// Type of the type constructor
    typ: Term,
    /// The type's value constructors
    consts: Vec<Binding>,
}

/// Top-level directive
enum Directive {
    /// Global name definition
    Define(DefineDirective),
    /// Inductive data type definition
    Data(DataDirective),
    /// Type debug print
    Check(Term),
    /// Value debug print
    Print(Term),
}

/// General-purpose binding between a type and value
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct TypeVal {
    typ: Term,
    val: Term,
}

/// A globally-defined name
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum GlobalBinding {
    /// A term and its type, such as from a define directive
    TypeVal(TypeVal),
    /// A constructor
    Const(Term),
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum Term {
    Type,
    Var(Var),
    App(Box<Term>, Box<Term>),
    Lambda(Abstraction),
    ForAll(Abstraction),
    /// Type annotation
    Ann(Box<TypeVal>),
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum Var {
    Global(String), // Globally-defined name
    Local(usize),   // De Bruijn index
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct Abstraction {
    binder_type: Box<Term>,
    body: Box<Term>,
}

/// Type and value context
#[derive(Clone)]
struct Context {
    /// Mapping of global names to values
    global_bindings: OrdMap<String, GlobalBinding>,
    /// Mapping of local bindings (De Bruijn indices) to their types.
    /// This vector is indexed as `vec[De Bruijn index - 1]`. Entering
    /// the scope of an abstraction during type checking prepends the
    /// abstraction's binder type to this.
    local_binding_types: Vec<Term>,
    /// Mapping of constructor names to their types
    constrs: OrdMap<String, Term>,
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Term::Type => write!(f, "Type"),
            Term::Var(var) => write!(f, "{}", var),
            Term::App(m, n) => write!(f, "({} {})", m, n),
            Term::Lambda(abs) => write!(f, "(lambda {})", abs),
            Term::ForAll(abs) => write!(f, "(forall {})", abs),
        }
    }
}

impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Var::Global(name) => write!(f, "{}", name),
            Var::Local(ind) => write!(f, "{}", ind),
        }
    }
}

impl fmt::Display for Abstraction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // TODO: Convert De-Brujin indices to names
        write!(f, "{} {}", self.binder_type, self.body)
    }
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

impl DefineDirective {
    fn from_sexpr_list(list: &[Sexpr]) -> Fallible<Self> {
        if let [name, typ, val] = list[1..] {
            let name = name
                .as_symbol()
                .ok_or_else(|| format_err!("name in define directive is not a symbol"))?
                .to_string();
            let typ = Term::from_sexpr(&typ)?;
            let val = Term::from_sexpr(&val)?;
            let type_val = TypeVal { typ, val };

            Ok(Self { name, type_val })
        } else {
            bail!("define directive has incorrect amount of arguments")
        }
    }

    fn eval(&self, ctx: &Context) -> Fallible<Context> {
        let TypeVal { typ, val } = self.type_val;

        let left = typ.beta_reduce(ctx)?;
        let right = val.get_type(ctx)?.beta_reduce(ctx)?;

        if left != right {
            bail!("type disagreement\n  left: {}\n  right: {}", left, right);
        }

        let binding = GlobalBinding::TypeVal(self.type_val);

        Ok(ctx.add_global_binding(&self.name, &binding))
    }
}

impl Binding {
    fn from_sexpr(sexpr: &Sexpr) -> Fallible<Self> {
        let list = sexpr_as_list(sexpr)
            .ok_or_else(|| format_err!("binding is not a list"))?
            .as_slice();

        if let [name, typ] = list {
            let name = name
                .as_symbol()
                .ok_or_else(|| format_err!("binding name is not a symbol"))?
                .to_string();
            let typ = Term::from_sexpr(typ)?;

            Ok(Self { name, typ })
        } else {
            bail!("invalid binding format")
        }
    }

    fn from_sexpr_map_list(list: &[Sexpr]) -> Fallible<Vec<Self>> {
        list.iter().map(|exp| Self::from_sexpr(exp)).collect()
    }

    fn from_sexpr_map(sexpr: &Sexpr) -> Fallible<Vec<Self>> {
        let list = sexpr_as_list(sexpr).ok_or_else(|| format_err!("expected list of bindings"))?;
        Self::from_sexpr_map_list(list)
    }
}

impl DataDirective {
    fn from_sexpr_list(list: &[Sexpr]) -> Fallible<Self> {
        if let [name, typ, consts] = list {
            let name = name
                .as_symbol()
                .ok_or_else(|| format_err!("name in data directive is not a symbol"))?
                .to_string();

            let typ = Term::from_sexpr(typ)?;

            let consts = Binding::from_sexpr_map(consts)?;

            Ok(Self { name, typ, consts })
        } else {
            bail!("data directive has incorrect amount of arguments")
        }
    }

    fn eval(&self, ctx: &Context) -> Fallible<Context> {
        // TODO: Define type constructor
        let ctx = ctx.add_global_binding(&self.name, &binding);

        // TODO: Define induction principle
        // TODO: Define value constructors
        // TODO: Various semantics checks
    }
}

impl Directive {
    fn define_from_sexpr_list(list: &[Sexpr]) -> Fallible<Self> {
        Ok(Directive::Define(DefineDirective::from_sexpr_list(list)?))
    }

    fn data_from_sexpr_list(list: &[Sexpr]) -> Fallible<Self> {
        Ok(Directive::Data(DataDirective::from_sexpr_list(list)?))
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
            "Data" => Directive::data_from_sexpr_list(list),
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

    fn eval_check(term: &Term, ctx: &Context) -> Fallible<()> {
        println!("type: {}", term.get_type(ctx)?);
        Ok(())
    }

    fn eval_print(term: &Term, ctx: &Context) -> Fallible<()> {
        println!("term: {}", term.beta_reduce(ctx)?);
        Ok(())
    }

    fn eval(&self, ctx: &Context) -> Fallible<Context> {
        match self {
            Directive::Define(def) => def.eval(ctx),
            Directive::Data(data) => data.eval(ctx),
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
                .get_global_binding(name)
                .ok_or_else(|| format_err!("variable '{}' not in scope", name))
                .map(|binding| binding.get_type()),
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
                .get_global_binding(name)
                .map(|binding| {
                    if let GlobalBinding::TypeVal(type_val) = binding {
                        type_val.val
                    } else {
                        Term::Var(Var::Global(name.to_owned()))
                    }
                })
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
            Term::Var(Var::Global(name)) => ctx.get_global_binding(name).is_none(),
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

impl GlobalBinding {
    /// Get the type of a global binding
    fn get_type(&self) -> Term {
        match self {
            &GlobalBinding::TypeVal(type_val) => type_val.typ,
            &GlobalBinding::Const(typ) => typ,
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
            global_bindings: OrdMap::new(),
            local_binding_types: Vec::new(),
            constrs: OrdMap::new(),
        }
    }

    fn add_global_binding(&self, name: &str, binding: &GlobalBinding) -> Self {
        let Self {
            global_bindings,
            local_binding_types,
            constrs,
        } = self.to_owned();

        let global_bindings = global_bindings.update(name.to_string(), binding.to_owned());

        Self {
            global_bindings,
            local_binding_types,
            constrs,
        }
    }

    fn enter_abstraction(&self, binding_type: &Term) -> Self {
        let Self {
            global_bindings,
            mut local_binding_types,
            constrs,
        } = self.to_owned();

        local_binding_types.push(binding_type.to_owned());

        Self {
            global_bindings,
            local_binding_types,
            constrs,
        }
    }

    /// Add a constructor to the context
    fn add_constr(&self, binding: &Binding) -> Self {}

    fn get_global_binding(&self, name: &str) -> Option<&GlobalBinding> {
        self.global_bindings.get(name)
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

fn sexpr_as_list(sexpr: &Sexpr) -> Option<&Vec<Sexpr>> {
    match sexpr {
        Sexpr::List(sexprs) => Some(sexprs),
        _ => None,
    }
}

fn expect_sexpr_list(sexpr: &Sexpr) -> &Vec<Sexpr> {
    sexpr_as_list(sexpr).expect("expected sexpr list")
}

fn try_main() -> Fallible<()> {
    let path = get_input_path();

    let code = std::fs::read_to_string(path)?;

    // Surround code with parens so there is a list of directives at
    // the top level
    let code = format!("( {} )", code);

    let sexprs = lexpr::from_str(&code)?;
    let sexprs = expect_sexpr_list(&sexprs);

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
