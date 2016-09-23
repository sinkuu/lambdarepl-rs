#![feature(question_mark)]

mod expr;

extern crate linefeed;
extern crate combine;
extern crate ansi_term;

use expr::Expr;
use linefeed::{Reader, Command};
use std::io::{self, Write};
use std::collections::HashMap;

fn main() {
    let mut reader = Reader::new("lambdarepl").unwrap();

    reader.set_prompt("[λ]> ");
    reader.set_blink_matching_paren(true);
    reader.bind_sequence("\\", Command::Macro("λ".into()));

    let mut variables = HashMap::<String, Expr>::new();

    while let Some(input) = reader.read_line().unwrap() {
        let input = input.trim();
        if input.is_empty() {
            continue;
        }

        reader.add_history(input.to_string());

        if input.starts_with(':') {
            let command = &input[1..];
            if command.starts_with("let ") {
                let idx = command.find('=').unwrap();
                let var = &command[4..idx].trim();
                let expr = match expr::parse(&command[idx+1..]) {
                    Ok(expr) => expr,
                    Err(e) => {
                        let mut stderr = io::stderr();
                        write!(stderr, "{}", ansi_term::Colour::Red.paint(format!("{}", e))).unwrap();
                        continue;
                    }
                };
                variables.insert(var.to_string(), expr);
            }

            continue;
        }

        let mut expr: Expr = match expr::parse(&input) {
            Ok(expr) => expr,
            Err(e) => {
                let mut stderr = io::stderr();
                write!(stderr, "{}", ansi_term::Colour::Red.paint(format!("{}", e))).unwrap();
                continue;
            }
        };

        for v in expr.clone().free_variables() {
            if let Some(val) = variables.get(v) {
                expr = expr.replace(&v, val.clone());
            }
        }

        loop {
            println!("{}", expr);
            let (b, e) = expr.reduce();
            expr = e;
            if !b { break; }
        }
        println!("");

        variables.insert("ANS".to_string(), expr);
    }
}
