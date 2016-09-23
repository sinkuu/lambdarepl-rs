use combine::{self, ParseResult, ParseError};
use std::fmt;
use std::collections::HashSet;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Var(String),
    Abs(String, Box<Expr>),
    App(Box<Expr>, Box<Expr>),
}

impl Expr {
    pub fn var(ident: &str) -> Expr {
        Expr::Var(ident.into())
    }

    pub fn abs(ident: &str, e: Expr) -> Expr {
        Expr::Abs(ident.into(), e.into())
    }

    pub fn app(func: Expr, input: Expr) -> Expr {
        Expr::App(func.into(), input.into())
    }

    pub fn is_var(&self) -> bool {
        if let Expr::Var(..) = *self {
            true
        } else {
            false
        }
    }

    pub fn is_abs(&self) -> bool {
        if let Expr::Abs(..) = *self {
            true
        } else {
            false
        }
    }

    pub fn is_app(&self) -> bool {
        if let Expr::App(..) = *self {
            true
        } else {
            false
        }
    }

    pub fn replace(self, from: &str, to: Expr) -> Expr {
        match self {
            Expr::Var(v) => if v == from { to } else { Expr::Var(v) },

            Expr::App(a, b) => {
                Expr::App(a.replace(from, to.clone()).into(),
                          b.replace(from, to).into())
            }

            Expr::Abs(v, e) => {
                if v == from {
                    Expr::Abs(v, e)
                } else {
                    if to.free_variables().contains(&*v) {
                        let newv = SubstituteVarNames::new()
                            .find(|x| x != &v)
                            .unwrap();
                        let e = e.replace(&v, Expr::Var(newv.clone()));
                        Expr::Abs(newv, e.replace(from, to).into())
                    } else {
                        Expr::Abs(v, e.replace(from, to).into())
                    }
                }
            }
        }
    }

    pub fn reduce(self) -> (bool, Expr) {
        match self {
            var @ Expr::Var(..) => (false, var),

            Expr::App(func, input) => {
                // rust-lang/rust#30564
                let func = *func;
                match func {
                    Expr::Abs(v, e) => (true, e.replace(&v, *input)),
                    a @ Expr::App(..) => {
                        let (b, a) = a.reduce();
                        if b {
                            (b, Expr::App(a.into(), input))
                        } else {
                            let (bi, input) = input.reduce();
                            (bi, Expr::App(a.into(), input.into()))
                        }
                    }
                    v @ Expr::Var(..) => {
                        let (b, input) = input.reduce();
                        (b, Expr::App(v.into(), input.into()))
                    }
                }
            }

            Expr::Abs(v, e) => {
                let (b, e) = e.reduce();
                (b, Expr::Abs(v, e.into()))
            }
        }
    }

    fn reduce_to_end(self) -> Expr {
        let mut expr = self;
        loop {
            let (b, e) = expr.reduce();
            expr = e;
            if !b {
                break;
            }
        }
        expr
    }

    pub fn free_variables(&self) -> HashSet<&str> {
        let mut set: HashSet<&str> = HashSet::new();

        match *self {
            Expr::Var(ref v) => {
                assert!(set.insert(v));
            }

            Expr::App(ref a, ref b) => {
                set.extend(a.free_variables().into_iter());
                set.extend(b.free_variables().into_iter());
            }

            Expr::Abs(ref v, ref e) => {
                let mut ev = e.free_variables();
                ev.remove(v.as_str());
                set.extend(ev.into_iter());
            }
        }

        set
    }
}

#[test]
fn test_reduction() {
    let two = parse("λf x. f (f x)").unwrap();
    let succ = parse("λn f x. f (n f x)").unwrap();
    let plus = parse("λm n f x. m f (n f x)").unwrap();
    let mult = parse("λm n. m (plus n) (λf x.x)")
        .unwrap()
        .replace("plus", plus.clone());

    let expr = parse(r"plus (succ two) two")
        .unwrap()
        .replace("plus", plus)
        .replace("two", two.clone())
        .replace("succ", succ.clone())
        .reduce_to_end();
    assert_eq!(format!("{}", expr), "λf x.(f (f (f (f (f x)))))");

    let expr = parse(r"mult two two")
        .unwrap()
        .replace("two", two)
        .replace("succ", succ)
        .replace("mult", mult)
        .reduce_to_end();
    assert_eq!(format!("{}", expr), "λf x.(f (f (f (f x))))");
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fn may_wrap(f: &mut fmt::Formatter, e: &Expr) -> fmt::Result {
            if e.is_abs() || e.is_app() {
                write!(f, "({})", e)
            } else {
                write!(f, "{}", e)
            }
        }

        match *self {
            Expr::Var(ref ident) => write!(f, "{}", ident)?,
            Expr::Abs(ref ident, ref expr) => {
                write!(f, "λ{}", ident)?;
                let mut expr = expr;
                while let Expr::Abs(ref i, ref e) = **expr {
                    write!(f, " {}", i)?;
                    expr = e;
                }
                write!(f, ".")?;
                may_wrap(f, expr)?;
            }
            Expr::App(ref func, ref input) => {
                if func.is_app() {
                    func.fmt(f)?;
                } else {
                    may_wrap(f, func)?;
                }
                write!(f, " ")?;
                may_wrap(f, input)?;

            }
        }

        Ok(())
    }
}

#[test]
fn test_expr_display() {
    use std::fmt::Write;

    let expr = Expr::abs("a",
                         Expr::app(Expr::var("a"), Expr::abs("x", Expr::var("x"))));

    let mut s = String::new();
    write!(s, "{}", expr).unwrap();
    assert_eq!(s, "λa.(a (λx.x))");
}

pub fn parse(s: &str) -> Result<Expr, ParseError<combine::State<&str>>> {
    use combine::{Parser, State, eof, parser, many1, many, between, try};
    use combine::char::{char, letter, spaces};
    use combine::range::take_while1;
    use std::string::ToString;

    fn parse_inner(s: State<&str>) -> ParseResult<Expr, State<&str>> {
        fn parse_expr(s: State<&str>) -> ParseResult<Expr, State<&str>> {
            let variable = take_while1(|c: char| c.is_alphabetic()).map(Expr::var);

            let abstruction = (char('\\')
                                   .or(char('λ'))
                                   .skip(spaces())
                                   .with(many1::<Vec<_>, _>(take_while1(|c: char| c.is_alphabetic())
                                       .skip(spaces()))),
                               char('.').skip(spaces()).with(parser(parse_inner)))
                .map(|(v, e)| {
                    debug_assert!(!v.is_empty());
                    let mut iter = v.into_iter().map(ToString::to_string).rev();
                    let last = iter.next().unwrap();
                    iter.fold(Expr::Abs(last, e.into()), |abs, v| Expr::Abs(v, abs.into()))
                });

            abstruction.or(variable)
                .or(between((char('('), spaces()),
                            (spaces(), char(')')),
                            parser(parse_inner)))
                .parse_stream(s)
        }

        let apps = (parser(parse_expr), many::<Vec<_>, _>(try(spaces().with(parser(parse_expr)))))
            .map(|(expr, apps)| {
                apps.into_iter().fold(expr, |acc, x| Expr::App(acc.into(), x.into()))
            });

        spaces()
            .with(apps)
            .skip(spaces())
            .parse_stream(s)
    }

    parser(parse_inner)
        .skip(eof())
        .parse(combine::State::new(s))
        .map(|(expr, _)| expr)
}


#[test]
fn test_parser() {
    assert_eq!(format!("{}", parse(r"\x.((\x.x) x y)").unwrap()),
               "λx.((λx.x) x y)");
    assert_eq!(format!("{}", parse(r"λx.(λx.x)(λy.y)(λz.z)").unwrap()),
               "λx.((λx.x) (λy.y) (λz.z))");
    assert_eq!(format!("{}",
                       parse(r"\ x.( ( ( \ x . x ) ( \ y . y ) ) ( \ z . z ) ) ").unwrap()),
               "λx.((λx.x) (λy.y) (λz.z))");
    assert_eq!(format!("{}", parse(r"\x y z.z").unwrap()), r"λx y z.z");
}

#[derive(Debug)]
struct SubstituteVarNames(usize);

impl SubstituteVarNames {
    fn new() -> SubstituteVarNames {
        SubstituteVarNames(0)
    }
}

impl Iterator for SubstituteVarNames {
    type Item = String;

    fn next(&mut self) -> Option<String> {
        let mut n = self.0;
        let mut s = vec![];

        self.0 += if n % 27 <= 1 { 2 } else { 1 };

        loop {
            let d = match n % 27 {
                0 => 0,
                d => d - 1,
            };

            s.push((b'a'..b'z' + 1).nth(d).unwrap());
            n /= 27;
            if n == 0 {
                return Some(s.into_iter().rev().map(|b| b as char).collect());
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (usize::max_value(), None)
    }
}

#[test]
fn test_substitute_var_names() {
    assert_eq!(SubstituteVarNames::new().skip(25).take(3).collect::<Vec<String>>(),
               vec!["z", "aa", "ab"]);
    assert_eq!(SubstituteVarNames::new().skip(26 + 26 * 26 - 1).take(3).collect::<Vec<String>>(),
               vec!["zz", "aaa", "aab"]);
}
