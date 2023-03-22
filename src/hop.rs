use egg::{Id, Language};

use crate::{EGraph, Math};
use std::collections::HashMap;

pub static HOP: &str = "29,29;80;LiteralOp 6.14;;0,0,-1,-1,-1;S;D;0,0,0,0;;;";

#[derive(Debug)]
pub struct Hop {
    id: u32,
    op: Math,
    children: Vec<u32>,
    row: u32,
    col: u32,
    nnz: Option<i32>,
}

fn op(s: &str, children: Vec<Id>) -> Option<Math> {
    match s {
        "r(t)" => Some(Math::LTrs([children[0]])),
        "b(*)" => Some(Math::LMul([children[0], children[1]])),
        "b(+)" => Some(Math::LAdd([children[0], children[1]])),
        "b(-)" => Some(Math::LMin([children[0], children[1]])),
        "ba(+*)" => Some(Math::MMul([children[0], children[1]])),
        "ua(+R)" => Some(Math::Srow([children[0]])),
        "ua(+C)" => Some(Math::Scol([children[0]])),
        "ua(+RC)" => Some(Math::Sall([children[0]])),
        _ => None,
    }
}

fn get_lit(s: &str) -> Option<Math> {
    if s.starts_with("LiteralOp") {
        let n: f64 = s.split_whitespace().nth(1).unwrap().parse().unwrap();
        Some(Math::Num(n.into()))
    } else {
        None
    }
}

fn get_var(s: &str) -> Option<Math> {
    if s.starts_with("TRead") {
        let v = s.split_whitespace().nth(1).unwrap();
        Some(Math::Str(v.to_owned()))
    } else {
        None
    }
}

fn get_write(s: &str) -> Option<Math> {
    if s.starts_with("TWrite") {
        let v = s.split_whitespace().nth(1).unwrap();
        Some(Math::TWrite(v.to_owned()))
    } else {
        None
    }
}

fn get_udf(s: &str) -> Option<Math> {
    Some(Math::Str(s.to_owned()))
}

pub fn parse_hop(s: &str) -> Hop {
    let hop: Vec<_> = s.split(";").collect();
    let id: u32 = hop[1].parse().unwrap();
    let op_s = hop[2];
    let children: Vec<u32> = hop[3].split(",").filter_map(|s| s.parse().ok()).collect();
    let op = op(
        op_s,
        children
            .iter()
            .cloned()
            .map(|i| Id::from(i as usize))
            .collect(),
    )
    .or(get_write(op_s))
    .or(get_var(op_s))
    .or(get_lit(op_s))
    .or(get_udf(op_s))
    .unwrap();

    let meta: Vec<Option<i32>> = hop[4].split(",").map(|s| s.parse().ok()).collect();
    let mut row = meta[0].unwrap_or(0);
    if row == 0 || row == -1 {
        row = 1
    };
    let mut col = meta[1].unwrap_or(0);
    if col == 0 || col == -1 {
        col = 1
    };
    let mut nnz = meta[4];
    if let Some(-1) = nnz {
        nnz = Some(row as i32 * col as i32)
    }

    Hop {
        id,
        op,
        children,
        row: row as u32,
        col: col as u32,
        nnz,
    }
}

pub fn load_dag(egraph: &mut EGraph, s: &str) -> Vec<Id> {
    use Math::*;
    let mut id_map = HashMap::new();
    let hops = s.lines();
    let mut roots = vec![];
    for h in hops {
        let hop = parse_hop(h);
        // TODO special case for literal, string
        match hop.op {
            Num(n) => {
                let s = format!("(llit {})", n);
                let exp = s.parse().unwrap();
                let lit = egraph.add_expr(&exp);
                id_map.insert(Id::from(hop.id as usize), lit);
            }
            Str(x) => {
                let mut args = hop
                    .children
                    .iter()
                    .map(|c| Id::from(*c as usize))
                    .collect::<Vec<_>>();
                if args.len() == 0 {
                    let m = format!(
                        "(lmat {x} {i} {j} {z})",
                        x = x,
                        i = hop.row,
                        j = hop.col,
                        z = hop.nnz.unwrap()
                    );
                    let exp = m.parse().unwrap();
                    let mat = egraph.add_expr(&exp);
                    id_map.insert(Id::from(hop.id as usize), mat);
                } else {
                    // add dimensions to children for rix / lix (right and left index)
                    if x == "rix" || x == "lix" {
                        let row = egraph.add(Math::Num((hop.row as f64).into()));
                        let col = egraph.add(Math::Num((hop.col as f64).into()));
                        args.push(row);
                        args.push(col);
                        id_map.insert(row, row);
                        id_map.insert(col, col);
                    }
                    let op_s = egraph.add(Math::Str(x));
                    let mut children = vec![op_s];
                    children.extend(args.iter().map(|c| id_map[c]));
                    let udf = egraph.add(Math::Udf(children));
                    id_map.insert(Id::from(hop.id as usize), udf);
                }
            }
            op => {
                // let children: Vec<_> = hop.children.iter().map(|c| id_map[c]).collect();
                let id = egraph.add(op.clone().map_children(|c| id_map[&c]));
                if let Math::TWrite(_) = op {
                    roots.push(id);
                }
                id_map.insert(Id::from(hop.id as usize), id);
            }
        }
    }
    roots
}

pub fn print_dag(egraph: &EGraph) {
    for c in egraph.classes() {
        let id = &c.id;
        for e in &c.nodes {
            match e {
                Math::Str(_) | Math::Num(_) => {
                    // println!("STRNUM id{} {:?}", id, op);
                }
                Math::Udf(children) => {
                    print!("0,0;{id};", id = id);
                    let f = children[0];
                    let op = format!("{:?}", &egraph[f].nodes[0]);
                    print!("{};", op);
                    //for e in &egraph[f].nodes {
                    //    print!("{};", e.op);
                    //}
                    let args = if op == "rix" {
                        &children[1..6]
                    } else if op == "lix" {
                        &children[1..7]
                    } else {
                        &children[1..]
                    };
                    for c in args {
                        print!("{},", c);
                    }
                    println!(";;M;D;;;;;")
                }
                Math::LMat([x, _, _, _]) => {
                    print!("0,0;{id};TRead ", id = id);
                    // let x = e.children[0];
                    for e in &egraph[*x].nodes {
                        print!("{:?}", e);
                    }
                    println!(";;;M;D;;;;;")
                }
                Math::LLit([x]) => {
                    print!("0,0;{id};LiteralOp ", id = id);
                    for c in e.children() {
                        for e in &egraph[*c].nodes {
                            print!("{:?}", e);
                        }
                    }
                    println!(";;;M;D;;;;;");
                }
                Math::TWrite(s) => {
                    print!("0,0;{id};TWrite {var};", id = id, var = s);
                    for c in e.children() {
                        print!("{},", c);
                    }
                    println!(";;M;D;;;;;")
                }
                Math::Var(_) => {
                    println!("var");
                }
                op => {
                    print!("0,0;{id};{op};", id = id, op = dml_op(op));
                    for c in e.children() {
                        print!("{},", c);
                    }
                    println!(";;M;D;;;;;");
                }
            }
        }
    }
}

fn dml_op(op: &Math) -> &'static str {
    match op {
        Math::LAdd(_) => "b(+)",
        Math::LMin(_) => "b(-)",
        Math::LMul(_) => "b(*)",
        Math::MMul(_) => "ba(+*)",
        Math::LTrs(_) => "r(t)",
        Math::Srow(_) => "ua(+R)",
        Math::Scol(_) => "ua(+C)",
        Math::Sall(_) => "ua(+RC)",
        // o => panic!("unknown op {:?}", o)
        o => {
            println!("UNK {}", o);
            "UNKNWON OP"
        }
    }
}

// 29,29;86;TRead B;;500000,10,1000,1000,5000000;M;D;0,0,38,-;;;

// 29,29;80;LiteralOp 6.14;;0,0,-1,-1,-1;S;D;0,0,0,0;;;
// LMat = "lmat", LLit = "llit", Udf = "udf", Var = "var"
