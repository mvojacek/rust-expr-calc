#![allow(unused_macros, unused_imports)]

extern crate num_traits;

use num_traits::Num;

#[macro_use]
mod macros;
mod splitkeep;
mod asdebug;
mod nodelinkedlist;

use self::splitkeep::SplitKeepingDelimiterExt;
use self::splitkeep::SplitType;
use std::fmt::Debug;
use std::fmt::Display;
use std::fmt::Formatter;
use std::fmt::Error;
use crate::nodelinkedlist::NodeList;
use crate::nodelinkedlist::Node;
use std::error;
use std::fmt;
use std::io;
use std::io::Write;
use std::fmt::Write as FmtWrite;

trait MyNum: Num + Debug + Display + Copy + Clone {}

impl<T: Num + Debug + Display + Copy + Clone> MyNum for T {}

fn main() {
    let mut buf = String::new();
    loop {
        print!("Enter: ");
        let _ = io::stdout().flush();
        match io::stdin().read_line(&mut buf) {
            Err(error) => {
                println!("error reading: {}", error);
                continue;
            }
            _ => {}
        }

        assert_eq!(buf.pop(), Some('\n')); //newline

        if buf.is_empty() {
            buf = "((3+4)*2+1)*(2+3*(2+3))".to_string();
        }

        println!("Expression: {}", buf);

        let result = calculate::<i64>(&buf, 10);

        match result {
            Ok(n) => println!("Calculated value: {}", n),
            Err(e) => match e.0 {
                None => println!("Error: {}", e.1),
                Some(idx) => println!("Error at token {}: {}", idx + 1, e.1),
            },
        };

        buf.clear()
    }
}

#[test]
fn test_calc_div_trunc() {
    assert_eq!(calculate10::<i64>(&"9/2".to_string()).unwrap(), 4);
}

#[test]
fn test_calc_precedence() {
    assert_eq!(calculate10::<i64>(&"5+6*7-9/2".to_string()).unwrap(), 43);
}

#[test]
fn test_calc_parens() {
    assert_eq!(calculate10::<i64>(&"(5+6)*7-9/2".to_string()).unwrap(), 73);
}

#[test]
fn test_calc_parens_lock() {
    assert_eq!(calculate10::<i64>(&"(3+4)*2+1+2+3*(2+3)".to_string()).unwrap(), 32);
}

#[test]
fn test_calc_parens_nested() {
    assert_eq!(calculate10::<i64>(&"((3+4)*2+1)*(2+3*(2+3))".to_string()).unwrap(), 255);
}

enum CalcErr<N: MyNum> {
    EmptyExpr,
    ParseInt(N::FromStrRadixErr),
    OpMissing,
    OpNoPrev,
    OpNoNext,
    OpBadPrev,
    OpBadNext,
    OpErr(Box<fmt::Display + Send>),
    ParenStray,
}

impl<N: MyNum> Display for CalcErr<N> where <N as Num>::FromStrRadixErr: Display {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        match self {
            CalcErr::EmptyExpr => f.write_str("Empty expression"),
            CalcErr::ParseInt(err) => f.write_fmt(format_args!("Number parse ({})", err)),
            CalcErr::OpMissing => f.write_str("Operator missing"),
            CalcErr::OpNoPrev => f.write_str("Operator missing left operand"),
            CalcErr::OpNoNext => f.write_str("Operator missing right operand"),
            CalcErr::OpBadPrev => f.write_str("Operator has bad left operand"),
            CalcErr::OpBadNext => f.write_str("Operator has bad right operand"),
            CalcErr::OpErr(e) => f.write_fmt(format_args!("Operator failed ({})", e)),
            CalcErr::ParenStray => f.write_str("Stray parenthesis"),
        }
    }
}

impl<N: MyNum> Debug for CalcErr<N> where CalcErr<N>: Display {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        Display::fmt(self, f)
    }
}

fn calculate10<N: MyNum>(expr: &String) -> Result<N, (Option<usize>, CalcErr<N>)> {
    calculate(expr, 10)
}

fn calculate<N: MyNum>(expr: &String, base: u32) -> Result<N, (Option<usize>, CalcErr<N>)> {
    let head = tokenize::<N>(expr, base).map_err(|e| (None, e))?.head.ok_or((None, CalcErr::EmptyExpr))?;

    let mut p = [true; 4]; //needPass

    loop {
        println!("{}", head);
        if p[0] {
            p[0] = operator_pass(&head, Op::Mul, |a, b| Ok(a * b))?;
            if paren_pass(&head)? {
                p = [true; 4];
                continue;
            };
            println!("{}", head);
        }

        if p[1] {
            p[1] = operator_pass(&head, Op::Div, |a, b| if !b.is_zero() { Ok(a / b) } else { Err(Box::new("Div by zero")) })?;
            if paren_pass(&head)? {
                p = [true; 4];
                continue;
            };
            println!("{}", head);
        }

        if p[2] {
            p[2] = operator_pass(&head, Op::Add, |a, b| Ok(a + b))?;
            if paren_pass(&head)? {
                p = [true; 4];
                continue;
            };
            println!("{}", head);
        }

        if p[3] {
            p[3] = operator_pass(&head, Op::Sub, |a, b| Ok(a - b))?;
            if paren_pass(&head)? {
                p = [true; 4];
                continue;
            };
            println!("{}", head);
        }

        if head.list_len() > 1 {
            if p.iter().find(|b| **b).is_none() {
                return Err((None, CalcErr::OpMissing));
            }
            continue;
        }

        break;
    }

    let expr = head.bor().data;
    match expr {
        Expr::Num { n, locked } => Ok(n),
        _ => unreachable!(),
    }
}

fn tokenize<N: MyNum>(expr: &String, base: u32) -> Result<NodeList<Expr<N>>, CalcErr<N>> {
    let delims = &['+', '*', '-', '/', '(', ')'][..];
    expr.split_keeping_delimiter(delims).map(|e| {
        match e {
            SplitType::Delimiter(s) => {
                let c = s.chars().next().unwrap_or_else(|| unreachable!());
                Ok(Paren::parse(c).map(Expr::from)
                    .or_else(|| Op::parse(c).map(Expr::from))
                    .unwrap_or_else(|| unreachable!()))
            }
            SplitType::Match(s) => {
                match N::from_str_radix(s, base) {
                    Ok(n) => Ok(n.into()),
                    Err(e) => Err(CalcErr::ParseInt(e))
                }
            }
        }
    }).collect()
}

fn operator_pass<N: MyNum, F>(head: &Node<Expr<N>>, op: Op, func: F) -> Result<bool, (Option<usize>, CalcErr<N>)>
    where F: Fn(N, N) -> Result<N, Box<fmt::Display + Send>> {
    let mut second_pass = false;
    head.list_iter()
        .enumerate()
        .filter(|(_, n)| n.use_value(|ex| *ex == Expr::Op(op)))
        .collect::<Vec<_>>()
        .into_iter()
        .try_for_each(|(idx, n)| {
            let prev = n.prev().ok_or((Some(idx), CalcErr::OpNoPrev))?;
            let next = n.next().ok_or((Some(idx), CalcErr::OpNoNext))?;

            let prev_n = match prev.bor().data {
                Expr::Paren(Paren::Close) => {
                    second_pass = true;
                    match &mut next.bor_mut().data {
                        Expr::Num { n, locked } => {
                            *locked = true
                        }
                        _ => {}
                    };
                    return Ok(());
                }
                Expr::Num { n, locked: false } => n,
                Expr::Num { n, locked: true } => return Ok(()),
                _ => return Err((Some(idx), CalcErr::OpBadPrev))
            };

            let next_n = match next.bor().data {
                Expr::Paren(Paren::Open) => {
                    second_pass = true;
                    match &mut prev.bor_mut().data {
                        Expr::Num { n, locked } => {
                            *locked = true
                        }
                        _ => {}
                    };
                    return Ok(());
                }
                Expr::Num { n, locked: false } => n,
                Expr::Num { n, locked: true } => return Ok(()),
                _ => return Err((Some(idx), CalcErr::OpBadNext))
            };

            let result = match func(prev_n, next_n) {
                Ok(n) => n,
                Err(e) => return Err((Some(idx), CalcErr::OpErr(e)))
            };
            println!("{} {} {} = {}", prev_n, op, next_n, result);

            next.cut();
            n.cut();
            prev.bor_mut().data = result.into();

            Ok(())
        })?;

    Ok(second_pass)
}

fn lock_pass<N: MyNum>(head: &Node<Expr<N>>) {
    head.list_iter()
        .filter_map(|n| n.use_value(|ex| match *ex {
            Expr::Paren(p) => Some(p),
            _ => None
        }).map(|p| (n, p)))
        .for_each(|(n, p)| {
            paren_mut_adjacent_num(&n, p, |num, locked| {
                *locked = true;
            })
        });
}

fn paren_pass<N: MyNum>(head: &Node<Expr<N>>) -> Result<bool, (Option<usize>, CalcErr<N>)> {
    let mut second_pass = false;
    head.list_iter()
        .enumerate()
        .filter(|(_, n)| n.use_value(|ex| *ex == Paren::Open.into()))
        .collect::<Vec<_>>()
        .into_iter()
        .try_for_each(|(idx, open_paren)| {
            let next = open_paren.next().ok_or((Some(idx), CalcErr::ParenStray))?;
            let num = match next.bor().data {
                Expr::Num { n, locked } => n,
                Expr::Paren(Paren::Open) => return Ok(()),
                _ => return Err((Some(idx), CalcErr::ParenStray)),
            };
            let close_paren = next.next().ok_or((Some(idx), CalcErr::ParenStray))?;
            match close_paren.bor().data {
                Expr::Paren(Paren::Close) => {}
                _ => return Ok(())
            };

            paren_mut_adjacent_num(&close_paren, Paren::Close, |n, locked| {
                *locked = false;
            });
            paren_mut_adjacent_num(&open_paren, Paren::Open, |n, locked| {
                *locked = false;
            });

            close_paren.cut();
            next.cut();
            open_paren.bor_mut().data = num.into();

            second_pass = true;

            Ok(())
        })?;

    lock_pass(head);

    Ok(second_pass)
}

fn paren_mut_adjacent_num<N: MyNum, F>(n: &Node<Expr<N>>, paren: Paren, func: F)
    where F: FnOnce(&mut N, &mut bool) {
    match paren {
        Paren::Open => {
            match n.prev() {
                Some(n) => n.use_value(|ex| {
                    match ex {
                        Expr::Op(_) => {
                            match n.prev() {
                                Some(n) => {
                                    match &mut n.bor_mut().data {
                                        Expr::Num { n, locked } => {
                                            func(n, locked);
                                        }
                                        _ => {}
                                    }
                                }
                                _ => {}
                            }
                        }
                        _ => {}
                    }
                }),
                _ => {}
            }
        }
        Paren::Close => {
            match n.next() {
                Some(n) => n.use_value(|ex| {
                    match ex {
                        Expr::Op(_) => {
                            match n.next() {
                                Some(n) => {
                                    match &mut n.bor_mut().data {
                                        Expr::Num { n, locked } => {
                                            func(n, locked);
                                        }
                                        _ => {}
                                    }
                                }
                                _ => {}
                            }
                        }
                        _ => {}
                    }
                }),
                _ => {}
            }
        }
    }
}

#[derive(Debug, Eq, PartialEq, Clone, Copy)]
enum Expr<N: MyNum> {
    Num { n: N, locked: bool },
    Op(Op),
    Paren(Paren),
}

impl<N: MyNum> Expr<N> {
    fn is_num(&self) -> bool {
        match *self {
            Expr::Num { n, locked } => true,
            _ => false,
        }
    }
    fn is_op(&self) -> bool {
        match *self {
            Expr::Op(_) => true,
            _ => false,
        }
    }
    fn is_paren(&self) -> bool {
        match *self {
            Expr::Paren(_) => true,
            _ => false,
        }
    }
}
/*
impl<N: MyNum + Display> Display for Expr<N> {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        match self {
            Expr::Num(n) => f.write_fmt(format_args!("Num({})", n)),
            Expr::Op(op) => f.write_fmt(format_args!("Op({})", op)),
            Expr::Paren(p) => f.write_fmt(format_args!("Paren({})", p))
        }
    }
}*/

impl<N: MyNum + Display> Display for Expr<N> {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        match self {
            Expr::Num { n, locked } => f.write_fmt(format_args!("{}{}", n, if *locked { "!" } else { "" })),
            Expr::Op(op) => f.write_fmt(format_args!("{}", op)),
            Expr::Paren(p) => f.write_fmt(format_args!("{}", p))
        }
    }
}

impl<N: MyNum> From<N> for Expr<N> {
    fn from(n: N) -> Self {
        Expr::Num { n, locked: false }
    }
}

impl<N: MyNum> From<Op> for Expr<N> {
    fn from(op: Op) -> Self {
        Expr::Op(op)
    }
}

impl<N: MyNum> From<Paren> for Expr<N> {
    fn from(p: Paren) -> Self {
        Expr::Paren(p)
    }
}

#[derive(Debug, Eq, PartialEq, Clone, Copy)]
enum Paren {
    Open,
    Close,
}

impl Display for Paren {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        f.write_char(self.char())
    }
}

impl Paren {
    fn parse(c: char) -> Option<Self> {
        match c {
            '(' => Some(Paren::Open),
            ')' => Some(Paren::Close),
            _ => None
        }
    }

    fn char(&self) -> char {
        match self {
            Paren::Open => '(',
            Paren::Close => ')',
        }
    }
}

#[derive(Debug, Eq, PartialEq, Clone, Copy)]
enum Op {
    Mul,
    Div,
    Add,
    Sub,
}

impl Display for Op {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        f.write_char(self.char())
    }
}

impl Op {
    fn parse(c: char) -> Option<Self> {
        match c {
            '*' => Some(Op::Mul),
            '/' => Some(Op::Div),
            '+' => Some(Op::Add),
            '-' => Some(Op::Sub),
            _ => None
        }
    }

    fn char(&self) -> char {
        match self {
            Op::Mul => '*',
            Op::Div => '/',
            Op::Add => '+',
            Op::Sub => '-',
        }
    }
}

