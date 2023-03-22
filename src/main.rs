use egg::{
    EGraph, //pattern::{Applier, Rewrite, WildMap},
    Extractor,
};
use log::*;
use warp::Meta;
use warp::{
    dag_cost, load_dag, optimize, parse_hop, print_dag, rules, trans_rules, untrans_rules, Math,
};

//use std::env;
use std::env;
use std::fs;

fn main() {
    let _ = env_logger::builder().is_test(false).try_init();
    let args: Vec<String> = env::args().collect();
    let hops = &args[1];
    let _ = env_logger::builder().is_test(true).try_init();
    let contents = fs::read_to_string(hops).expect("Something went wrong reading the file");

    let mut egraph = EGraph::new(Meta::default());
    let root = load_dag(&mut egraph, &contents);
    let sol = optimize(egraph, &root, true, false, false);

    for s in sol.iter() {
        let sol_s = s.pretty(80);
        //println!("{}", sol_s);
    }
    let mut egraph = EGraph::new(Meta::default());
    for s in sol.iter() {
        egraph.add_expr(&s);
    }
    print_dag(&egraph);
}
