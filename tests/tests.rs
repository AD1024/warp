use warp::{Math, EGraph, rules, trans_rules, extract};
use egg::{
    define_term,
    egraph::{AddResult, EClass, Metadata},
    expr::{Expr, Language, QuestionMarkName},
    extract::{calculate_cost, Extractor},
    parse::ParsableLanguage,
    pattern::{Applier, Rewrite, WildMap},
};
use log::*;

fn prove_something(size_limit: usize, start: &str, goals: &[&str]) {
    let _ = env_logger::builder().is_test(true).try_init();

    let start_expr = Math::parse_expr(start).unwrap();
    println!("Start ({}): {}", calculate_cost(&start_expr), start);

    let goal_exprs: Vec<_> = goals.iter().map(|g| Math::parse_expr(g).unwrap()).collect();

    let (mut egraph, root) = EGraph::from_expr(&start_expr);

    let rules = rules();
    let mut egraph_size = 0;
    for i in 0..500 {
        println!("\nIteration {}:", i);
        println!(
            "Size n={}, e={}",
            egraph.total_size(),
            egraph.number_of_classes()
        );

        let ext = Extractor::new(&egraph);
        let best = ext.find_best(root);
        println!("Best ({}): {}", best.cost, best.expr.pretty(40));
        let new_size = egraph.total_size();
        if new_size == egraph_size {
            println!("\nEnding early because we're saturated");
            break;
        }
        if new_size > size_limit {
            println!("\nStop because size limit of {}", size_limit);
            break;
        }
        egraph_size = new_size;

        for rw in &rules {
            let new = rw.run(&mut egraph).len();
            if new > 0 {
                println!("Fired {} {} times", rw.name, new);
            }
        }
        egraph.rebuild();
    }

    egraph.dump_dot("test.dot");

    for (i, (goal_expr, goal_str)) in goal_exprs.iter().zip(goals).enumerate() {
        info!("Trying to prove goal {}: {}", i, goal_str);
        let equivs = egraph.equivs(&start_expr, &goal_expr);
        if equivs.is_empty() {
            panic!("Couldn't prove goal {}: {}", i, goal_str);
        }
    }
}
#[test]
fn lambda_avoid() {
    prove_something(
        5_000,
        "(subst (dim i 1) (dim j 2) (sum (dim k 3) (sum (dim l 4) (lit 0))))",
        &["(sum (dim k 3) (sum (dim l 4) (subst (dim i 1) (dim j 2) (lit 0))))"],
    );
}
#[test]
fn schema() {
    prove_something(
        5_000,
        "(dim k 3)",
        &["(dim k 3)"],
    );
}

#[test]
fn sum_i_a() {
    prove_something(
        5_000,
        "(sum (dim i 10) (mat x (dim j 9) (dim k 8) (nnz 0)))",
        &["(*  (mat x (dim j 9) (dim k 8) (nnz 0)) (lit 10))"],
    );
}

#[test]
fn dim_subst() {
    prove_something(
        5_000,
        "(subst (dim j 10) (dim i 10) (dim i 10))",
        &["(dim j 10)"],
    );
}

#[should_panic(expected = "Couldn't prove goal 0")]
#[test]
fn dim_subst_fail() {
    prove_something(
        5_000,
        "(subst (dim j 10) (dim i 10) (dim k 10))",
        &["(dim j 10)"],
    );
}


#[test]
fn pull_mul() {
    prove_something(
        5_000,
        "(sum (dim i 10) (* (mat y (dim j 9) (dim k 8) (nnz 0)) (mat x (dim i 9) (dim k 8) (nnz 0))))",
        &["(*(mat y (dim j 9) (dim k 8) (nnz 0)) (sum (dim i 10)  (mat x (dim i 9) (dim k 8) (nnz 0))))"],
    );
}


//#[test]
fn push_mul() {
    prove_something(
        5_000,
        "(* (mat a (dim i 10) (dim j 10) (nnz 0)) (sum (dim i 10) (mat b (dim i 10) (dim k 10) (nnz 0))))",
        &[ "(sum (dim v734493 10) (* (mat a (dim i 10) (dim j 10) (nnz 0)) (mat b (dim v734493 10) (dim k 10) (nnz 0)))) "],
    );
}

#[test]
fn push_mul_2() {
    prove_something(
        5_000,
        "(* (mat a (dim k 10) (dim j 10)(nnz 0)) (sum (dim i 10) (mat b (dim i 10) (dim k 10)(nnz 0))))",
        &[ "(sum (dim i 10) (* (mat a (dim k 10) (dim j 10)(nnz 0))  (mat b (dim i 10) (dim k 10)(nnz 0)))) "],
    );
}

#[test]
fn test_extract() {
    let start = "(* (lit 1) (* (lit 1) (* (lit 1) (* (lit 1) (* (lit 1) (* (lit 1) (* (lit 1) (lit 1))))))))";
    println!("input: {:?}", start);
    let start_expr = Math::parse_expr(start).unwrap();
    let (mut egraph, root) = EGraph::from_expr(&start_expr);

    let rules = rules();
    for i in 1..50 {
        for rw in &rules {
            rw.run(&mut egraph);
        }
    }

    let best = extract(egraph, root);
    println!("{}", best.pretty(80));
}

//#[test]
fn parrot() {
    prove_something(
        5_000,
        "(sum (dim j 1000000) (sum (dim k 500000) (* \
         (+ (mat x (dim j 1000000) (dim k 500000) (nnz 500)) (sum (dim i 10) (* (mat u (dim j 1000000) (dim i 10) (nnz 10000000)) (mat v (dim i 10) (dim k 500000) (nnz 5000000))))) \
         (+ (mat x (dim j 1000000) (dim k 500000) (nnz 500)) (sum (dim i 10) (* (mat u (dim j 1000000) (dim i 10) (nnz 10000000)) (mat v (dim i 10) (dim k 500000) (nnz 5000000))))))))",
        &[ "lol"],
    );
}

//#[test]
fn extract_parrot() {
    let _ = env_logger::builder().is_test(true).try_init();
    let start = "(sum (dim j 1000000) (sum (dim k 500000) (* \
     (+ (mat (var x) (dim j 1000000) (dim k 500000) (nnz 500)) (sum (dim i 10) (* (mat (var u) (dim j 1000000) (dim i 10) (nnz 10000000)) (mat (var v) (dim i 10) (dim k 500000) (nnz 5000000))))) \
     (+ (mat (var x) (dim j 1000000) (dim k 500000) (nnz 500)) (sum (dim i 10) (* (mat (var u) (dim j 1000000) (dim i 10) (nnz 10000000)) (mat (var v) (dim i 10) (dim k 500000) (nnz 5000000))))))))";
    println!("input: {:?}", start);
    let start_expr = Math::parse_expr(start).unwrap();
    let (mut egraph, root) = EGraph::from_expr(&start_expr);

    let rules = rules();
    for i in 1..50 {
        for rw in &rules {
            println!("APPLYING {}", rw.name);
            rw.run(&mut egraph);
        }
        egraph.rebuild();
    }

    let best = extract(egraph, root);
    println!("{}", best.pretty(80));
}

#[test]
fn la_input() {
    let _ = env_logger::builder().is_test(true).try_init();
    // "sum((x + 2uv)^2)"
    let start = "(sall (l*\
                       (l+ (lmat x 1000000 500000 500)\
                        (l* (llit 2) (m* (lmat u 1000000 10 1000000)\
                                      (lmat v 10 500000 500000))))\
                       (l+ (lmat x 1000000 500000 500)\
                        (l* (llit 2) (m* (lmat u 1000000 10 1000000)\
                                      (lmat v 10 500000 500000))))))";
    let start_expr = Math::parse_expr(start).unwrap();
    let (mut egraph, root) = EGraph::from_expr(&start_expr);
}

#[test]
fn l_mul() {
    let _ = env_logger::builder().is_test(true).try_init();
    // "sum((x + 2uv)^2)"
    let start = "(l* (llit 2) (m* (lmat u 1000000 10 1000000)\
                                      (lmat v 10 500000 500000)))";
    let start_expr = Math::parse_expr(start).unwrap();
    let (mut egraph, root) = EGraph::from_expr(&start_expr);
}

#[test]
fn l_add() {
    let _ = env_logger::builder().is_test(true).try_init();
    // "sum((x + 2uv)^2)"
    let start = "(l+ (lmat x 1000000 500000 500)\
                        (l* (llit 2) (m* (lmat u 1000000 10 1000000)\
                                      (lmat v 10 500000 500000))))";
    let start_expr = Math::parse_expr(start).unwrap();
    let (mut egraph, root) = EGraph::from_expr(&start_expr);
}

#[test]
fn test_translate() {
    let _ = env_logger::builder().is_test(true).try_init();
    let start = "(sall (l*\
                       (l+ (lmat x 1000000 500000 500)\
                        (l* (llit 2) (m* (lmat u 1000000 10 1000000)\
                                      (lmat v 10 500000 500000))))\
                       (l+ (lmat x 1000000 500000 500)\
                        (l* (llit 2) (m* (lmat u 1000000 10 1000000)\
                                      (lmat v 10 500000 500000))))))";
    let start_expr = Math::parse_expr(start).unwrap();
    let (mut egraph, root) = EGraph::from_expr(&start_expr);

    let rules = trans_rules();
    for i in 1..50 {
        for rw in &rules {
            println!("APPLYING {}", rw.name);
            rw.run(&mut egraph);
        }
        egraph.rebuild();
    }

    let ext = Extractor::new(&egraph);
    let best = ext.find_best(root);

    println!("best is {}",best.expr.pretty(100));
}

#[test]
fn translate_ladd() {
    let _ = env_logger::builder().is_test(true).try_init();
    let start = "(l+ (lmat x 1000000 500000 500)\
                        (l* (llit 2) (m* (lmat u 1000000 10 1000000)\
                                      (lmat v 10 500000 500000))))";
    let start_expr = Math::parse_expr(start).unwrap();
    let (mut egraph, root) = EGraph::from_expr(&start_expr);

    let rules = trans_rules();
    for i in 1..50 {
        for rw in &rules {
            println!("APPLYING {}", rw.name);
            rw.run(&mut egraph);
        }
        egraph.rebuild();
    }

    egraph.dump_dot("trans.dot");
    //let best = extract(egraph, root);
}

#[test]
fn translate_lmul() {
    let _ = env_logger::builder().is_test(true).try_init();
    let start = "(l* (llit 2) (m* (lmat u 1000000 10 1000000)\
                                      (lmat v 10 500000 500000)))";
    let start_expr = Math::parse_expr(start).unwrap();
    let (mut egraph, root) = EGraph::from_expr(&start_expr);

    let rules = trans_rules();
    for i in 1..3 {
        for rw in &rules {
            println!("APPLYING {}", rw.name);
            rw.run(&mut egraph);
        }
        egraph.rebuild();
    }

    egraph.dump_dot("lmul.dot");
    //let best = extract(egraph, root);
}

#[test]
fn translate_mmul() {
    let _ = env_logger::builder().is_test(true).try_init();
    let start = "(m* (lmat u 1000000 10 1000000)\
                                      (lmat v 10 500000 500000))";
    let start_expr = Math::parse_expr(start).unwrap();
    let (mut egraph, root) = EGraph::from_expr(&start_expr);

    let rules = trans_rules();
    for i in 1..50 {
        for rw in &rules {
            println!("APPLYING {}", rw.name);
            rw.run(&mut egraph);
        }
        egraph.rebuild();
    }

    egraph.dump_dot("trans.dot");
    //let best = extract(egraph, root);
}

#[test]
fn test_bind() {
    let _ = env_logger::builder().is_test(true).try_init();
    let start = "(b+ i j (b- i j (b+ i j (lmat x 10 10 10))))";
    let start_expr = Math::parse_expr(start).unwrap();
    let (mut egraph, root) = EGraph::from_expr(&start_expr);

    let rules = trans_rules();
    for i in 1..50 {
        for rw in &rules {
            println!("APPLYING {}", rw.name);
            rw.run(&mut egraph);
        }
        egraph.rebuild();
    }

    egraph.dump_dot("bind.dot");
    //let best = extract(egraph, root);
}

#[test]
fn test_lmul_simp() {
    let _ = env_logger::builder().is_test(true).try_init();
    let start = "(l* (lmat x 20 10 20) (llit 2))";
    let start_expr = Math::parse_expr(start).unwrap();
    let (mut egraph, root) = EGraph::from_expr(&start_expr);

    let rules = trans_rules();
    for i in 1..50 {
        for rw in &rules {
            println!("APPLYING {}", rw.name);
            rw.run(&mut egraph);
        }
        //egraph.rebuild();
    }

    egraph.dump_dot("lmul.dot");
    //let best = extract(egraph, root);
}
