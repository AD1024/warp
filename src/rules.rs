use crate::{EGraph, Math, Meta, Schema};

use egg::{rewrite as rw, Applier, Pattern, Rewrite, Var};

use std::collections::hash_map::DefaultHasher;
use std::collections::HashSet;
use std::hash::{Hash, Hasher};

#[rustfmt::skip]
pub fn untrans_rules() -> Vec<Rewrite<Math, Meta>> {
    vec![
        rw!("ra-minus"; "(l+ ?a (l* (llit -1) ?b))" => "(l- ?a ?b)"),
        rw!("ra-elim-bind0"; "(b- ?i ?j (b+ ?i ?j ?x))" => "?x"),
        // rw("ra-elim-bind1", "(b+ ?i ?j (b- ?i _ ?x))", "?x"),
        // rw("ra-elim-bind2", "(b+ ?i ?j (b- _ ?j ?x))", "?x"),
        // rw("ra-elim-bind3", "(b+ ?i ?j (b- _ _ ?x))", "?x"),
        rw!("ra-unbind-lit"; "(b- ?i ?j (lit ?n))" => "(llit ?n)"),
        rw!("ra_sall"; "(srow (scol ?x))" => "(sall ?x)"),
        rw!("ra_sall2"; "(scol (srow ?x))" => "(sall ?x)"),
        rw!("ra_mat1"; "(mat ?x (dim ?i ?n) (dim ?j ?m) (nnz ?z))" => "(b+ ?i ?j (lmat ?x ?n ?m ?z))"),
        //rw("ra_mat2", "(mat ?x (dim ?i ?n) (dim ?j ?m) (nnz ?z))", "(b+ ?j ?i (lmat ?x ?m ?n ?z))"),
        rw!("ra_transpose"; "(b- ?j ?i (b+ ?i ?j ?x))" => "(trans ?x)"),
        rw!("ra_lit"; "(lit ?n)" => "(b+ _ _ (llit ?n))"),
        rw!("sum_d1"; "(sum (dim _ 1) ?x)" => "?x"),
        // TODO(mike): fix these
        rw!("ra-bind"; "?e" => { RABind { e: "?e".parse().unwrap() } }),
        rw!("ra-add"; "(+ ?a ?b)" => { RAAdd { a: "?a".parse().unwrap(), b: "?b".parse().unwrap() } }),
        rw!("ra-mul"; "(* ?a ?b)" => { RAMul { a: "?a".parse().unwrap(), b: "?b".parse().unwrap() } }),
        rw!("ra-sum"; "(sum ?i ?x)" => { RASum { i: "?i".parse().unwrap(), x: "?x".parse().unwrap() } }),
        rw!("ra-mmul2"; "(rm* ?a ?b)" => { RARMMul { a: "?a".parse().unwrap(), b: "?b".parse().unwrap() } }),
    ]
}

#[rustfmt::skip]
pub fn trans_rules() -> Vec<Rewrite<Math, Meta>> {
    vec![
        // TODO b(^) is probability parsed as b (^)
        rw!("la-sq"; "(udf b(^) ?x (llit 2))"=> "(l* ?x ?x)"),
        rw!("la-minus"; "(l- ?a ?b)"=> "(l+ ?a (l* (llit -1) ?b))"),
        rw!("la-mat-bind"; "(b+ ?k ?l (lmat ?x ?i ?j ?z))"=> "(mat ?x (dim ?k ?i) (dim ?l ?j) (nnz ?z))"),
        rw!("la-lit-bind";  "(b+ ?i ?j (llit ?n))"=>            "(lit ?n)"),
        rw!("la-lit-ubnd";  "(llit ?n)"=>                       "(b- _ _ (lit ?n))"),
        rw!("subst-+";      "(subst ?e ?v (+ ?a ?b))"=>         "(+ (subst ?e ?v ?a) (subst ?e ?v ?b))"),
        rw!("subst-*";      "(subst ?e ?v (* ?a ?b))"=>         "(* (subst ?e ?v ?a) (subst ?e ?v ?b))"),
        rw!("subst-matrix"; "(subst ?e ?v (mat ?a ?i ?j ?z))"=> "(mat ?a (subst ?e ?v ?i) (subst ?e ?v ?j) ?z)"),
        rw!("subst-lit";    "(subst ?e ?v (lit ?n))"=>          "(lit ?n)"),
        rw!("subst-var";    "(subst ?e ?v (var ?n))"=>          "(var ?n)"),
        rw!("subst-udf1";   "(subst ?e ?v (udf ?op ?x))"=>       "(udf ?op (subst ?e ?v ?x))"),
        rw!("subst-udf2";   "(subst ?e ?v (udf ?op ?x ?y))"=>    "(udf ?op (subst ?e ?v ?x) (subst ?e ?v ?y))"),
        rw!("subst-udf3";   "(subst ?e ?v (udf ?op ?x ?y ?z))"=> "(udf ?op (subst ?e ?v ?x) (subst ?e ?v ?y) (subst ?e ?v ?z))"),
        rw!("subst-udf4";   "(subst ?e ?v (udf ?op ?x ?y ?z ?u))"=> "(udf ?op (subst ?e ?v ?x) (subst ?e ?v ?y) (subst ?e ?v ?z) (subst ?e ?v ?u))"),
        rw!("subst-udf5";   "(subst ?e ?v (udf ?op ?x ?y ?z ?u ?w))"=>
           "(udf ?op (subst ?e ?v ?x) (subst ?e ?v ?y) (subst ?e ?v ?z) (subst ?e ?v ?u) (subst ?e ?v ?w))"),
        rw!("subst-udf6";   "(subst ?e ?v (udf ?op ?x ?y ?z ?u ?w ?a))"=>
           "(udf ?op (subst ?e ?v ?x) (subst ?e ?v ?y) (subst ?e ?v ?z) (subst ?e ?v ?u) (subst ?e ?v ?w) (subst ?e ?v ?a))"),
        rw!("subst-rix";   "(subst ?e ?v (udf ?op ?x ?y ?z ?u ?w ?a ?b))"=>
           "(udf rix (subst ?e ?v ?x) (subst ?e ?v ?y) (subst ?e ?v ?z) (subst ?e ?v ?u) (subst ?e ?v ?w) ?a ?b)"),
        rw!("subst-udf8";   "(subst ?e ?v (udf ?op ?x ?y ?z ?u ?w ?a ?b ?c))"=>
           "(udf lix (subst ?e ?v ?x) (subst ?e ?v ?y) (subst ?e ?v ?z) (subst ?e ?v ?u) (subst ?e ?v ?w) (subst ?e ?v ?a) ?b ?c)"),
        // NOTE this makes a loop and will triger stack overflow
        rw!("subst-wild"; "(subst (dim _ ?i) (dim _ ?j) ?e)"=> "?e"),
        // TODO(mike): fix these
        rw!("la_lmat";     "(lmat ?x ?i ?j ?z)" => { LAMat {
            x: "?x".parse().unwrap(),
            i: "?i".parse().unwrap(),
            j: "?j".parse().unwrap(),
            z: "?z".parse().unwrap(),
            } }),
        rw!("la_mul"; "(l* ?x ?y)" => {LAMul {
            x: "?x".parse().unwrap(),
            y: "?y".parse().unwrap(),
        }}),
        rw!("la_add"; "(l+ ?x ?y)" => {LAAdd {
            x: "?x".parse().unwrap(),
            y: "?y".parse().unwrap(),
        }}),
        rw!("la_mmul";"(m* ?x ?y)" => {LAMMul {
            x: "?x".parse().unwrap(),
            y: "?y".parse().unwrap(),
        }}),
        rw!("la-srow"; "(srow ?a)" => {LASrow {
            a: "?a".parse().unwrap(),
        }}),
        rw!("la-scol"; "(scol ?a)" => {LAScol {
            a: "?a".parse().unwrap(),
        }}),
        rw!("la-sall"; "(sall ?a)" => {LASall {
            a: "?a".parse().unwrap(),
        }}),
        rw!("la-trans"; "(trans ?a)" => {LATrans {
            a: "?a".parse().unwrap(),
        }}),
        rw!("la-bind"; "(b+ ?k ?l (b- ?i ?j ?x))" => {LABind {
            k: "?k".parse().unwrap(),
            l: "?l".parse().unwrap(),
            i: "?i".parse().unwrap(),
            j: "?j".parse().unwrap(),
            x: "?x".parse().unwrap(),
        }}),
        rw!("subst-bind"; "(subst (dim ?j ?m) (dim ?i ?n) (b+ ?k ?l ?e))" => {SubstBind {
            k: "?k".parse().unwrap(),
            l: "?l".parse().unwrap(),
            i: "?i".parse().unwrap(),
        }}),
        rw!("agg-subst"; "(subst ?e ?v1 (sum ?v2 ?body))" => {SubstAgg {
            e: "?e".parse().unwrap(),
            v1: "?v1".parse().unwrap(),
            v2: "?v2".parse().unwrap(),
            body: "?body".parse().unwrap(),
        }}),
        rw!("dim_subst"; "(subst ?e (dim ?v ?m) (dim ?i ?n))" => {DimSubst {
            e: "?e".parse().unwrap(),
            v: "?v".parse().unwrap(),
            i: "?i".parse().unwrap(),
            n: "?n".parse().unwrap(),
        }}),
    ]
}

#[rustfmt::skip]
pub fn rules() -> Vec<Rewrite<Math, Meta>> {
    vec![
        // NOTE subst e v x is x[v => e]
        // NOTE udf b(m1mul) breaks b/c parsing
        // rw("bindudf", "(b+ ?i ?j (udf ?o ?x ?y))", "(b+ ?i ?j (udf ?o (b- ?i ?j (b+ ?i ?j ?x)) (b- ?i ?j (b+ ?i ?j ?y))))"),
        // drw("la-bind", "(b+ ?k ?l (b- ?i ?j ?x))", LABind),
        rw!("trivial-id"; "(sum ?w (* (ind ?x (mat ?i ?w ?w ?n)) (mat ?i ?w ?w ?n)))" => "?x"),
        rw!("+-commutative"; "(+ ?a ?b)" => "(+ ?b ?a)"),
        rw!("*-commutative"; "(* ?a ?b)" => "(* ?b ?a)"),
        rw!("associate-+r+"; "(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)"),
        rw!("associate-+l+"; "(+ (+ ?a ?b) ?c)" => "(+ ?a (+ ?b ?c))"),
        rw!("associate-*r*"; "(* ?a (* ?b ?c))" => "(* (* ?a ?b) ?c)"),
        rw!("associate-*l*"; "(* (* ?a ?b) ?c)" => "(* ?a (* ?b ?c))"),
        rw!("subst-+";      "(subst ?e ?v (+ ?a ?b))" =>     "(+ (subst ?e ?v ?a) (subst ?e ?v ?b))"),
        rw!("subst-*";      "(subst ?e ?v (* ?a ?b))" =>     "(* (subst ?e ?v ?a) (subst ?e ?v ?b))"),
        rw!("add-2-mul"; "(+ ?x ?x)" => "(* (lit 2) ?x)"),
        rw!("subst-matrix"; "(subst ?e ?v (mat ?a ?i ?j ?z))" => "(mat ?a (subst ?e ?v ?i) (subst ?e ?v ?j) ?z)"),
        rw!("subst-lit";    "(subst ?e ?v (lit ?n))" =>      "(lit ?n)"),
        rw!("subst-var";    "(subst ?e ?v (var ?n))" =>      "(var ?n)"),
        rw!("distribute-lft-in";    "(* ?a (+ ?b ?c))" =>        "(+ (* ?a ?b) (* ?a ?c))"),
        rw!("distribute-rgt-in";    "(* ?a (+ ?b ?c))" =>        "(+ (* ?b ?a) (* ?c ?a))"),
        rw!("distribute-lft-out";   "(+ (* ?a ?b) (* ?a ?c))" => "(* ?a (+ ?b ?c))"),
        rw!("distribute-lft-out--"; "(- (* ?a ?b) (* ?a ?c))" => "(* ?a (- ?b ?c))"),
        rw!("distribute-rgt-out";   "(+ (* ?b ?a) (* ?c ?a))" => "(* ?a (+ ?b ?c))"),
        rw!("distribute-rgt-out--"; "(- (* ?b ?a) (* ?c ?a))" => "(* ?a (- ?b ?c))"),
        rw!("distribute-lft1-in";   "(+ (* ?b ?a) ?a)" =>        "(* (+ ?b (lit 1)) ?a)"),
        rw!("distribute-rgt1-in";   "(+ ?a (* ?c ?a))" =>        "(* (+ ?c (lit 1)) ?a)"),
        rw!("pullup-add";    "(sum ?i (+ ?a ?b))" =>            "(+ (sum ?i ?a) (sum ?i ?b))"),
        rw!("pushdown-add";  "(+ (sum ?i ?a) (sum ?i ?b))" =>  "(sum ?i (+ ?a ?b))"),
        rw!("swap-agg"; "(sum ?i (sum ?j ?a))" => "(sum ?j (sum ?i ?a))"),
        rw!("sum_"; "(sum (dim _ 1) ?x)" => "(* (lit 1) ?x)"),
        // TODO(mike): fix these
        rw!("sum_i_a"; "(sum ?i ?a)" => {SumIA {
            i: "?i".parse().unwrap(),
            a: "?a".parse().unwrap(),
        }}),
        rw!("pullup_mul"; "(sum ?i (* ?a ?b))" => {PullMul {
            i: "?i".parse().unwrap(),
            a: "?a".parse().unwrap(),
        }}),
        rw!("pushdown_mul"; "(* ?a (sum ?i ?b))" => {PushMul {
            i: "?i".parse().unwrap(),
            a: "?a".parse().unwrap(),
            b: "?b".parse().unwrap(),
        }}),
        rw!("agg-subst"; "(subst ?e ?v1 (sum ?v2 ?body))" => {SubstAgg {
            e: "?e".parse().unwrap(),
            v1: "?v1".parse().unwrap(),
            v2: "?v2".parse().unwrap(),
            body: "?body".parse().unwrap(),
        }}),
        rw!("dim_subst"; "(subst ?e (dim ?v ?m) (dim ?i ?n))" => {DimSubst {
            e: "?e".parse().unwrap(),
            v: "?v".parse().unwrap(),
            i: "?i".parse().unwrap(),
            n: "?n".parse().unwrap(),
        }}),
        rw!("mmul"; "(sum ?j (* ?a ?b))" => {AggMMul {
            j: "?j".parse().unwrap(),
            a: "?a".parse().unwrap(),
            b: "?b".parse().unwrap(),
        }}),
        rw!("subst-bind"; "(subst (dim ?j ?m) (dim ?i ?n) (b+ ?k ?l ?e))" => {SubstBind {
            i: "?i".parse().unwrap(),
            k: "?k".parse().unwrap(),
            l: "?l".parse().unwrap(),
        }}),
        // END
        // drw("m1mul", "(+ (lit 1) (* (lit -1) (* ?x ?y)))", MOneMul),
        // drw("axpy", "(+ ?x (* ?p ?y))", Axpy),
        // drw("sprop", "(* ?x (+ (lit 1) (* (lit -1) ?x)))", Sprop),
        // drw("udf_rename", "(b+ ?i ?j (udf ?o (b- ?k ?l ?x) (b- ?m ?n ?y)))", UdfRn),
        // TODO need bind ubnd below
        // rw("selp", "(* ?x (b+ ?i ?j (udf b(>) (b- ?k ?l ?x) (b- _ _ (lit 0)))))", "(b+ ?i ?j (udf selp (b- ?k ?l ?x)))"),
        // rw!("selp";
        //      "(* ?x (b+ ?i ?j (udf b(>) (b- ?k ?l ?x) (b- _ _ (lit 0))))))" =>
        //      "(b+ ?i ?j (udf selp (b- ?k ?l ?x)))"),
        // Rewrite::simple_rewrite(
        //     "selp",
        //     {
        //         let x = Math::parse_pattern("?x").unwrap();
        //         let i = Math::parse_pattern("?i").unwrap();
        //         let j = Math::parse_pattern("?j").unwrap();
        //         Pattern::Expr(op("*", vec![
        //             x,
        //             Pattern::Expr(op("b+", vec![
        //                 i,
        //                 j,
        //                 Pattern::Expr(Expr::new("udf".parse().unwrap(), vec![
        //                     Pattern::Expr(Expr::new(Math::Str("b(>)".to_owned()), vec![].into()).into()),
        //                     Math::parse_pattern("(b- ?k ?l ?x)").unwrap(),
        //                     Math::parse_pattern("(b- ?w ?v (lit 0))").unwrap(),
        //                 ].into()).into())
        //             ]))
        //         ]))},
        //     Math::parse_pattern("(b+ ?i ?j (udf selp (b- ?k ?l ?x)))").unwrap()
        // ),
    ]
}

#[derive(Debug)]
struct Axpy {
    x: Var,
    p: Var,
    y: Var,
}
impl Applier<Math, Meta> for Axpy {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<Math, Meta>,
        eclass: egg::Id,
        subst: &egg::Subst,
    ) -> Vec<egg::Id> {
        let x = subst[self.x];
        let p = subst[self.p];
        let y = subst[self.y];
        let x_schema = egraph[x].data.as_ref().unwrap().get_schm();
        let p_schema = egraph[p].data.as_ref().unwrap().get_schm();
        let y_schema = egraph[y].data.as_ref().unwrap().get_schm();
        if p_schema.is_empty() && x_schema.len() == 2 && x_schema == y_schema {
            let mut x_schema = x_schema.keys();
            let wc = "_".to_owned();
            let i = x_schema.next().unwrap_or(&wc).clone();
            let j = x_schema.next().unwrap_or(&wc).clone();

            let mut bind_ij = format!(
                "(b+ {i} {j} (udf axpy (b- {i} {j} ?x) (b- _ _ ?p) (b- {i} {j} ?y)))",
                i = &i,
                j = &j
            )
            .parse::<Pattern<Math>>()
            .unwrap()
            .apply_one(egraph, eclass, subst);

            let bind_ji = format!(
                "(b+ {j} {i} (udf axpy (b- {j} {i} ?x) (b- _ _ ?p) (b- {j} {i} ?y)))",
                i = &i,
                j = &j
            )
            .parse::<Pattern<Math>>()
            .unwrap()
            .apply_one(egraph, eclass, subst);
            return vec![bind_ij, bind_ji].concat();
        }
        return vec![];
    }
}

#[derive(Debug)]
struct UdfRn {
    i: Var,
    j: Var,
    k: Var,
    l: Var,
    m: Var,
    n: Var,
    x: Var,
    y: Var,
}

impl Applier<Math, Meta> for UdfRn {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<Math, Meta>,
        eclass: egg::Id,
        subst: &egg::Subst,
    ) -> Vec<egg::Id> {
        // (b+ ?i ?j (udf ?o (b- ?k ?l ?x) (b- ?m ?n ?y)))
        let i = subst[self.i];
        let i_str = egraph[i].data.schema.as_ref().unwrap().get_name();
        let j = subst[self.j];
        let j_str = egraph[j].data.schema.as_ref().unwrap().get_name();
        let k = subst[self.k];
        let k_str = egraph[k].data.schema.as_ref().unwrap().get_name();
        let l = subst[self.l];
        let l_str = egraph[l].data.schema.as_ref().unwrap().get_name();
        let m = subst[self.m];
        let m_str = egraph[m].data.schema.as_ref().unwrap().get_name();
        let n = subst[self.n];
        let n_str = egraph[n].data.schema.as_ref().unwrap().get_name();
        let x = subst[self.x];
        let x_schema = egraph[x].data.schema.as_ref().unwrap().get_schm();
        let y = subst[self.y];
        let y_schema = egraph[y].data.schema.as_ref().unwrap().get_schm();

        let subxi = if k_str == "_" || k_str == i_str {
            "?x".to_owned()
        } else {
            format!("(subst (dim ?i {n}) (dim ?k {n}) ?x)", n = x_schema[k_str])
        };
        let subxj = if l_str == "_" || l_str == j_str {
            subxi
        } else {
            format!(
                "(subst (dim ?j {n}) (dim ?l {n}) {sxi})",
                n = x_schema[l_str],
                sxi = subxi
            )
        };
        let subyi = if m_str == "_" || m_str == i_str {
            "?y".to_owned()
        } else {
            format!("(subst (dim ?i {n}) (dim ?m {n}) ?y)", n = y_schema[m_str])
        };
        let subyj = if n_str == "_" || n_str == j_str {
            subyi
        } else {
            format!(
                "(subst (dim ?j {n}) (dim ?n {n}) {syi})",
                n = y_schema[n_str],
                syi = subyi
            )
        };
        let (xi, xa) = if k_str == "_" {
            ("_", 1)
        } else {
            ("?i", x_schema[k_str])
        };
        let (xj, xb) = if l_str == "_" {
            ("_", 1)
        } else {
            ("?j", x_schema[l_str])
        };
        let (yi, ya) = if m_str == "_" {
            ("_", 1)
        } else {
            ("?i", y_schema[m_str])
        };
        let (yj, yb) = if n_str == "_" {
            ("_", 1)
        } else {
            ("?j", y_schema[n_str])
        };

        format!(
            "(b+ ?i ?j (udf ?o (b- {xi} {xj} {sxj}) (b- {yi} {yj} {syj})))",
            xi = xi,
            xj = xj,
            yi = yi,
            yj = yj,
            sxj = subxj,
            syj = subyj,
        )
        .parse::<Pattern<Math>>()
        .unwrap()
        .apply_one(egraph, eclass, subst)
    }
}

#[derive(Debug)]
struct Sprop {
    x: Var,
}

impl Applier<Math, Meta> for Sprop {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<Math, Meta>,
        eclass: egg::Id,
        subst: &egg::Subst,
    ) -> Vec<egg::Id> {
        // (b+ i j (sprop (b- i j ?x)))
        let x = subst[self.x];
        let mut x_schema = egraph[x].data.schema.as_ref().unwrap().get_schm().keys();
        if x_schema.len() <= 2 {
            let wc = "_".to_owned();
            let i = x_schema.next().unwrap_or(&wc).clone();
            let j = x_schema.next().unwrap_or(&wc).clone();

            let bind_ij = format!("(b+ {i} {j} (udf sprop (b- {i} {j} ?x)))", i = &i, j = &j)
                .parse::<Pattern<Math>>()
                .unwrap()
                .apply_one(egraph, eclass, subst);

            let bind_ji = format!("(b+ {j} {i} (udf sprop (b- {j} {i} ?x)))", i = &i, j = &j)
                .parse::<Pattern<Math>>()
                .unwrap()
                .apply_one(egraph, eclass, subst);
            return vec![bind_ij, bind_ji].concat();
        }
        vec![]
    }
}

#[derive(Debug)]
struct MOneMul {
    x: Var,
    y: Var,
}
impl Applier<Math, Meta> for MOneMul {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<Math, Meta>,
        eclass: egg::Id,
        subst: &egg::Subst,
    ) -> Vec<egg::Id> {
        // drw("m1mul", "(+ (lit 1) (* (lit -1) (* ?x ?y)))", MOneMul),
        // (b+ i j (udf m1mul (b- i j x) (b- i j y)))
        // get x schema, unbind
        // get y schema, unbind
        // get result schema, bind

        let x = subst[self.x];
        let y = subst[self.y];
        let new_node = Math::Mul([x, y]);
        let mul = egraph.add(new_node);
        let mut mul_schema = egraph[mul.id]
            .data
            .schema
            .as_ref()
            .unwrap()
            .get_schm()
            .keys();

        if mul_schema.len() <= 2 {
            let wc = "_".to_owned();
            let i = mul_schema.next().unwrap_or(&wc).clone();
            let j = mul_schema.next().unwrap_or(&wc).clone();

            let bind_ij = format!(
                "(b+ {i} {j} (udf m1mul (b- {i} {j} ?x) (b- {i} {j} ?y)))",
                i = &i,
                j = &j
            )
            .parse::<Pattern<Math>>()
            .unwrap()
            .apply_one(egraph, eclass, subst);

            let mut bind_ji = format!(
                "(b+ {j} {i} (udf m1mul (b- {j} {i} ?x) (b- {j} {i} ?y)))",
                i = &i,
                j = &j
            )
            .parse::<Pattern<Math>>()
            .unwrap()
            .apply_one(egraph, eclass, subst);
            return vec![bind_ij, bind_ji].concat();
        }
        vec![]
    }
}

#[derive(Debug)]
struct AggMMul {
    j: Var,
    a: Var,
    b: Var,
}

impl Applier<Math, Meta> for AggMMul {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<Math, Meta>,
        eclass: egg::Id,
        subst: &egg::Subst,
    ) -> Vec<egg::Id> {
        let j = subst[self.j];
        let a = subst[self.a];
        let b = subst[self.b];

        let a_schema = &egraph[a].data.schema.as_ref().unwrap().get_schm().clone();
        let a_s: HashSet<_> = a_schema.keys().cloned().collect();
        let b_schema = &egraph[b].data.schema.as_ref().unwrap().get_schm().clone();
        let b_s: HashSet<_> = b_schema.keys().cloned().collect();
        let i: Vec<_> = a_s.intersection(&b_s).collect();
        let j_schema = &egraph[j].data.schema.as_ref().unwrap().get_dims().0.clone();

        if a_schema.len() <= 2 && b_schema.len() <= 2 && i.len() == 1 && i[0] == j_schema {
            format!("(rm* ?a ?b)")
                .parse::<Pattern<Math>>()
                .unwrap()
                .apply_one(egraph, eclass, subst)
        } else {
            vec![]
        }
    }
}

#[derive(Debug)]
struct Foundit;

impl Applier<Math, Meta> for Foundit {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<Math, Meta>,
        eclass: egg::Id,
        subst: &egg::Subst,
    ) -> Vec<egg::Id> {
        panic!("FOUNDITTT")
    }
}

#[derive(Debug)]
struct SubstAgg {
    v1: Var,
    v2: Var,
    e: Var,
    body: Var,
}

impl Applier<Math, Meta> for SubstAgg {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<Math, Meta>,
        eclass: egg::Id,
        subst: &egg::Subst,
    ) -> Vec<egg::Id> {
        let v1 = subst[self.v1];
        let v2 = subst[self.v2];
        let e = subst[self.e];
        let body = subst[self.body];

        let res = if v1 == v2 {
            egraph.add(Math::Agg([v2, body]))
        } else {
            let sub_body = egraph.add(Math::Sub([e, v1, body]));
            egraph.add(Math::Agg([v2, sub_body]))
        };

        vec![res]
    }
}

// drw("subst-bind", "(subst (dim ?j ?m) (dim ?i ?n) (b+ ?k ?l ?e))", SubstBind),
#[derive(Debug)]
struct SubstBind {
    i: Var,
    k: Var,
    l: Var,
}
impl Applier<Math, Meta> for SubstBind {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<Math, Meta>,
        eclass: egg::Id,
        subst: &egg::Subst,
    ) -> Vec<egg::Id> {
        let i = subst[self.i];
        let k = subst[self.k];
        let l = subst[self.l];

        if i == k {
            format!("(b+ ?j ?l ?e)")
                .parse::<Pattern<Math>>()
                .unwrap()
                .apply_one(egraph, eclass, subst)
        } else if i == l {
            format!("(b+ ?k ?j ?e)")
                .parse::<Pattern<Math>>()
                .unwrap()
                .apply_one(egraph, eclass, subst)
        } else {
            format!("(b+ ?k ?l ?e)")
                .parse::<Pattern<Math>>()
                .unwrap()
                .apply_one(egraph, eclass, subst)
        }
    }
}

#[derive(Debug)]
struct SumIA {
    i: Var,
    a: Var,
}
impl Applier<Math, Meta> for SumIA {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<Math, Meta>,
        eclass: egg::Id,
        subst: &egg::Subst,
    ) -> Vec<egg::Id> {
        let i = subst[self.i];
        let i_m = &egraph[i].data;
        let (k, n) = i_m.schema.as_ref().unwrap().get_dims();

        let a = subst[self.a];
        let a_m = &egraph[a].data;
        let body = a_m.schema.as_ref().unwrap().get_schm();

        if !body.contains_key(k) {
            format!("(* ?a (lit {n}))", n = *n as i32)
                .parse::<Pattern<Math>>()
                .unwrap()
                .apply_one(egraph, eclass, subst)
        } else {
            vec![]
        }
    }
}

#[derive(Debug)]
struct PullMul {
    i: Var,
    a: Var,
}

impl Applier<Math, Meta> for PullMul {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<Math, Meta>,
        eclass: egg::Id,
        subst: &egg::Subst,
    ) -> Vec<egg::Id> {
        let i = subst[self.i];
        let i_schema = &egraph[i].data;
        let k = i_schema.schema.as_ref().unwrap().get_dims().0;

        let a = subst[self.a];
        let a_schema = &egraph[a].data;
        let body = a_schema.schema.as_ref().unwrap().get_schm();

        if !body.contains_key(k) {
            "(* ?a (sum ?i ?b))"
                .parse::<Pattern<Math>>()
                .unwrap()
                .apply_one(egraph, eclass, subst)
        } else {
            vec![]
        }
    }
}

#[derive(Debug)]
struct PushMul {
    i: Var,
    a: Var,
    b: Var,
}
impl Applier<Math, Meta> for PushMul {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<Math, Meta>,
        eclass: egg::Id,
        subst: &egg::Subst,
    ) -> Vec<egg::Id> {
        let a = subst[self.a];
        let i = subst[self.i];
        let b = subst[self.b];

        let (i_s, i_n) = egraph[i].data.schema.as_ref().unwrap().get_dims();
        let a_schema = egraph[a].data.schema.as_ref().unwrap().get_schm();

        if !a_schema.contains_key(i_s) {
            "(sum ?i (* ?a ?b))"
                .parse::<Pattern<Math>>()
                .unwrap()
                .apply_one(egraph, eclass, subst)
        } else {
            let mut s = DefaultHasher::new();
            [i, a, b].hash(&mut s);
            let fresh_s = format!("v{s}", s = &(s.finish() % 976521).to_string());

            format!(
                "(sum (dim {fv} {fn}) (* ?a (subst (dim {fv} {fn}) ?i ?b)))",
                fv=&fresh_s, fn=*i_n as i32
            )
            .parse::<Pattern<Math>>()
            .unwrap()
            .apply_one(egraph, eclass, subst)
        }
    }
}

#[derive(Debug)]
struct DimSubst {
    e: Var,
    v: Var,
    i: Var,
    n: Var,
}
impl Applier<Math, Meta> for DimSubst {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<Math, Meta>,
        eclass: egg::Id,
        subst: &egg::Subst,
    ) -> Vec<egg::Id> {
        let e = subst[self.e];
        let v = subst[self.v];
        let i = subst[self.i];
        let n = subst[self.n];
        if i != v {
            vec![egraph.add(Math::Dim([i, n]))]
        } else {
            vec![]
        }
        // let res = if i == v {
        //     AddResult {
        //         was_there: true,
        //         id: e,
        //     }
        // } else {
        //     egraph.add(Expr::new(Math::Dim, smallvec![i, n]))
        // };

        // vec![res]
    }
}

#[derive(Debug)]
struct LAMul {
    x: Var,
    y: Var,
}

impl Applier<Math, Meta> for LAMul {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<Math, Meta>,
        eclass: egg::Id,
        subst: &egg::Subst,
    ) -> Vec<egg::Id> {
        let x = subst[self.x];
        let y = subst[self.y];
        let x_schema = egraph[x].data.clone().schema.unwrap();
        let (x_i, x_j) = x_schema.get_mat();
        let y_schema = egraph[y].data.clone().schema.unwrap();
        let (y_i, y_j) = y_schema.get_mat();

        let mut s = DefaultHasher::new();
        [x, y].hash(&mut s);
        let fresh_s = (s.finish() % 976521).to_string();
        let fresh_i = format!("vmul_i{}", &fresh_s);
        let fresh_j = format!("vmul_j{}", &fresh_s);

        let bind_xi = if *x_i == 1 { "_" } else { &fresh_i };
        let bind_xj = if *x_j == 1 { "_" } else { &fresh_j };
        let bind_yi = if *y_i == 1 { "_" } else { &fresh_i };
        let bind_yj = if *y_j == 1 { "_" } else { &fresh_j };
        let ubnd_i = if x_i * y_i == 1 { "_" } else { &fresh_i };
        let ubnd_j = if x_j * y_j == 1 { "_" } else { &fresh_j };

        format!(
            "(b- {i} {j} (* (b+ {xi} {xj} ?x) (b+ {yi} {yj} ?y)))",
            i = ubnd_i,
            j = ubnd_j,
            xi = bind_xi,
            xj = bind_xj,
            yi = bind_yi,
            yj = bind_yj
        )
        .parse::<Pattern<Math>>()
        .unwrap()
        .apply_one(egraph, eclass, subst)
    }
}

#[derive(Debug)]
struct LAMat {
    x: Var,
    i: Var,
    j: Var,
    z: Var,
}
impl Applier<Math, Meta> for LAMat {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<Math, Meta>,
        eclass: egg::Id,
        subst: &egg::Subst,
    ) -> Vec<egg::Id> {
        // (lmat x i j z)
        let x = subst[self.x];
        let i = subst[self.i];
        let j = subst[self.j];
        let z = subst[self.z];

        let i_schema = egraph[i].data.clone().schema.unwrap();
        let x_i = i_schema.get_size();
        let j_schema = egraph[j].data.clone().schema.unwrap();
        let x_j = j_schema.get_size();

        let mut s = DefaultHasher::new();
        [x, i, j, z].hash(&mut s);
        let fresh_s = (s.finish() % 976521).to_string();
        let fresh_i = format!("vmat_i{}", &fresh_s);
        let fresh_j = format!("vmat_j{}", &fresh_s);
        let bind_i = if *x_i == 1 { "_" } else { &fresh_i };
        let bind_j = if *x_j == 1 { "_" } else { &fresh_j };

        format!(
            "(b- {i} {j} (mat ?x (dim {i} ?i) (dim {j} ?j) (nnz ?z)))",
            i = bind_i,
            j = bind_j
        )
        .parse::<Pattern<Math>>()
        .unwrap()
        .apply_one(egraph, eclass, subst)
    }
}

#[derive(Debug)]
struct LAAdd {
    x: Var,
    y: Var,
}

impl Applier<Math, Meta> for LAAdd {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<Math, Meta>,
        eclass: egg::Id,
        subst: &egg::Subst,
    ) -> Vec<egg::Id> {
        let x = subst[self.x];
        let y = subst[self.y];

        let x_schema = egraph[x].data.clone().schema.unwrap();
        let y_schema = egraph[y].data.clone().schema.unwrap();

        let (x_i, x_j) = x_schema.get_mat();
        let (y_i, y_j) = y_schema.get_mat();

        let mut s = DefaultHasher::new();
        [x, y].hash(&mut s);
        let fresh_s = (s.finish() % 976521).to_string();
        let fresh_i = "vadd_i".to_owned() + &fresh_s;
        let fresh_j = "vadd_j".to_owned() + &fresh_s;

        let bind_xi = if *x_i == 1 { "_" } else { &fresh_i };
        let bind_xj = if *x_j == 1 { "_" } else { &fresh_j };
        let bind_yi = if *y_i == 1 { "_" } else { &fresh_i };
        let bind_yj = if *y_j == 1 { "_" } else { &fresh_j };

        let ubnd_i = if x_i * y_i == 1 { "_" } else { &fresh_i };
        let ubnd_j = if x_j * y_j == 1 { "_" } else { &fresh_j };

        // [-i,j] (* [i,j]A [i,j]B)
        format!(
            "(b- {i} {j} (+ (b+ {xi} {xj} ?x) (b+ {yi} {yj} ?y)))",
            i = &ubnd_i,
            j = &ubnd_j,
            xi = &bind_xi,
            xj = &bind_xj,
            yi = &bind_yi,
            yj = &bind_yj
        )
        .parse::<Pattern<Math>>()
        .unwrap()
        .apply_one(egraph, eclass, subst)
    }
}

#[derive(Debug)]
struct LAMMul {
    x: Var,
    y: Var,
}
impl Applier<Math, Meta> for LAMMul {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<Math, Meta>,
        eclass: egg::Id,
        subst: &egg::Subst,
    ) -> Vec<egg::Id> {
        let x = subst[self.x];
        let y = subst[self.y];

        let x_schema = egraph[x].data.clone().schema.unwrap();
        let y_schema = egraph[y].data.clone().schema.unwrap();

        let (x_i, x_j) = x_schema.get_mat();
        let (y_j, y_k) = y_schema.get_mat();

        let mut s = DefaultHasher::new();
        [x, y].hash(&mut s);
        let fresh_s = (s.finish() % 976521).to_string();
        let fresh_i = "vmmul_i".to_owned() + &fresh_s;
        let fresh_j = "vmmul_j".to_owned() + &fresh_s;
        let fresh_k = "vmmul_k".to_owned() + &fresh_s;

        let bind_xi = if *x_i == 1 { "_" } else { &fresh_i };
        let bind_xj = if *x_j == 1 { "_" } else { &fresh_j };
        let bind_yj = if *y_j == 1 { "_" } else { &fresh_j };
        let bind_yk = if *y_k == 1 { "_" } else { &fresh_k };

        let ubnd_i = if *x_i == 1 { "_" } else { &fresh_i };
        let ubnd_k = if *y_k == 1 { "_" } else { &fresh_k };

        let agg_j = if x_j * y_j == 1 { "_" } else { &fresh_j };

        if agg_j == "_" {
            format!(
                "(b- {i} {k} (* (b+ {xi} {xj} ?x) (b+ {yj} {yk} ?y)))",
                i = &ubnd_i,
                k = &ubnd_k,
                xi = &bind_xi,
                xj = &bind_xj,
                yj = &bind_yj,
                yk = &bind_yk
            )
            .parse::<Pattern<Math>>()
            .unwrap()
            .apply_one(egraph, eclass, subst)
        } else {
            format!(
                "(b- {i} {k} (sum (dim {j} {j_n}) (* (b+ {xi} {xj} ?x) (b+ {yj} {yk} ?y))))",
                i = &ubnd_i,
                k = &ubnd_k,
                j = &agg_j,
                j_n = *x_j as i32,
                xi = &bind_xi,
                xj = &bind_xj,
                yj = &bind_yj,
                yk = &bind_yk,
            )
            .parse::<Pattern<Math>>()
            .unwrap()
            .apply_one(egraph, eclass, subst)
        }
    }
}

#[derive(Debug)]
struct LATrans {
    a: Var,
}

impl Applier<Math, Meta> for LATrans {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<Math, Meta>,
        eclass: egg::Id,
        subst: &egg::Subst,
    ) -> Vec<egg::Id> {
        let a = subst[self.a];
        let a_schema = egraph[a].data.schema.as_ref().unwrap();
        let (a_i, a_j) = a_schema.get_mat();

        let mut s = DefaultHasher::new();
        [a].hash(&mut s);
        let fresh_s = (s.finish() % 976521).to_string();
        let fresh_i = "vtrans_i".to_owned() + &fresh_s;
        let fresh_j = "vtrans_j".to_owned() + &fresh_s;

        let bind_ai = if *a_i == 1 { "_" } else { &fresh_i };
        let bind_aj = if *a_j == 1 { "_" } else { &fresh_j };

        format!("(b- {j} {i} (b+ {i} {j} ?a))", j = &bind_aj, i = &bind_ai)
            .parse::<Pattern<Math>>()
            .unwrap()
            .apply_one(egraph, eclass, subst)
    }
}

#[derive(Debug)]
struct LASrow {
    a: Var,
}

impl Applier<Math, Meta> for LASrow {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<Math, Meta>,
        eclass: egg::Id,
        subst: &egg::Subst,
    ) -> Vec<egg::Id> {
        let a = subst[self.a];
        let a_schema = egraph[a].data.schema.as_ref().unwrap();
        let (a_i, a_j) = a_schema.get_mat();

        let mut s = DefaultHasher::new();
        [a].hash(&mut s);
        let fresh_s = (s.finish() % 976521).to_string();
        let fresh_i = "vsrow_i".to_owned() + &fresh_s;
        let fresh_j = "vsrow_j".to_owned() + &fresh_s;

        let bind_ai = if *a_i == 1 { "_" } else { &fresh_i };
        let bind_aj = if *a_j == 1 { "_" } else { &fresh_j };

        format!(
            "(b- {i} _ (sum (dim {j} {jn}) (b+ {i} {j} ?a)))",
            i = &bind_ai,
            jn = *a_j as i32,
            j = &bind_aj
        )
        .parse::<Pattern<Math>>()
        .unwrap()
        .apply_one(egraph, eclass, subst)
    }
}

#[derive(Debug)]
struct LAScol {
    a: Var,
}

impl Applier<Math, Meta> for LAScol {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<Math, Meta>,
        eclass: egg::Id,
        subst: &egg::Subst,
    ) -> Vec<egg::Id> {
        let a = subst[self.a];
        let a_schema = egraph[a].data.schema.as_ref().unwrap();
        let (a_i, a_j) = a_schema.get_mat();

        let mut s = DefaultHasher::new();
        [a].hash(&mut s);
        let fresh_s = (s.finish() % 976521).to_string();
        let fresh_i = "vsrow_i".to_owned() + &fresh_s;
        let fresh_j = "vsrow_j".to_owned() + &fresh_s;

        let bind_ai = if *a_i == 1 { "_" } else { &fresh_i };
        let bind_aj = if *a_j == 1 { "_" } else { &fresh_j };

        format!(
            "(b- _ {j} (sum (dim {i} {in}) (b+ {i} {j} ?a)))",
            i=&bind_ai, in=*a_i as i32, j=&bind_aj
        )
        .parse::<Pattern<Math>>()
        .unwrap()
        .apply_one(egraph, eclass, subst)
    }
}

#[derive(Debug)]
struct LASall {
    a: Var,
}

impl Applier<Math, Meta> for LASall {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<Math, Meta>,
        eclass: egg::Id,
        subst: &egg::Subst,
    ) -> Vec<egg::Id> {
        let a = subst[self.a];
        let a_schema = egraph[a].data.schema.as_ref().unwrap();
        let (a_i, a_j) = a_schema.get_mat();

        let mut s = DefaultHasher::new();
        [a].hash(&mut s);
        let fresh_s = (s.finish() % 976521).to_string();
        let fresh_i = "vsall_i".to_owned() + &fresh_s;
        let fresh_j = "vsall_j".to_owned() + &fresh_s;

        let bind_ai = if *a_i == 1 { "_" } else { &fresh_i };
        let bind_aj = if *a_j == 1 { "_" } else { &fresh_j };

        format!(
            "(b- _ _ (sum (dim {i} {in}) (sum (dim {j} {jn}) (b+ {i} {j} ?a))))",
            i=&bind_ai, in=*a_i as i32, j=&bind_aj, jn=*a_j as i32
        )
        .parse::<Pattern<Math>>()
        .unwrap()
        .apply_one(egraph, eclass, subst)
    }
}

#[derive(Debug)]
struct LABind {
    i: Var,
    j: Var,
    k: Var,
    l: Var,
    x: Var,
}

impl Applier<Math, Meta> for LABind {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<Math, Meta>,
        eclass: egg::Id,
        subst: &egg::Subst,
    ) -> Vec<egg::Id> {
        let i = subst[self.i];
        let j = subst[self.j];
        let k = subst[self.k];
        let l = subst[self.l];
        let x = subst[self.x];

        let i_schema = egraph[i].data.schema.as_ref().unwrap().get_name();
        let j_schema = egraph[j].data.schema.as_ref().unwrap().get_name();
        let k_schema = egraph[k].data.schema.as_ref().unwrap().get_name();
        let l_schema = egraph[l].data.schema.as_ref().unwrap().get_name();
        let x_schema = egraph[x].data.schema.as_ref().unwrap().get_schm();
        let (x_i, x_j) = (
            *x_schema.get(i_schema).unwrap_or(&1),
            *x_schema.get(j_schema).unwrap_or(&1),
        );

        if l_schema == "_" {
            assert_eq!(j_schema, "_", "unbinding wildcard");
        }
        if k_schema == "_" {
            assert_eq!(i_schema, "_", "unbinding wildcard");
        }

        format!(
            "(subst (dim {l} {jn}) (dim {j} {jn}) (subst (dim {k} {in}) (dim {i} {in}) ?x))",
            l=&l_schema.clone(), jn=x_j as i32, j=&j_schema.clone(),
            k=&k_schema.clone(), in=x_i as i32, i=&i_schema.clone()
        )
        .parse::<Pattern<Math>>()
        .unwrap()
        .apply_one(egraph, eclass, subst)
    }
}

#[derive(Debug)]
struct RAAdd {
    a: Var,
    b: Var,
}

impl Applier<Math, Meta> for RAAdd {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<Math, Meta>,
        eclass: egg::Id,
        subst: &egg::Subst,
    ) -> Vec<egg::Id> {
        let a = subst[self.a];
        let b = subst[self.b];
        let add = egraph.add(Math::Add([a, b]));
        egraph.rebuild();
        let mut add_schema = egraph[add].data.schema.as_ref().unwrap().get_schm().keys();

        if add_schema.len() <= 2 {
            let wc = "_".to_owned();
            let i = add_schema.next().unwrap_or(&wc).clone();
            let j = add_schema.next().unwrap_or(&wc).clone();
            // TODO change this as mul

            let bind_ij = format!(
                "(b+ {i} {j} (l+ (b- {i} {j} ?a) (b- {i} {j} ?b)))",
                i = &i,
                j = &j
            )
            .parse::<Pattern<Math>>()
            .unwrap()
            .apply_one(egraph, eclass, subst);

            let bind_ji = format!(
                "(b+ {j} {i} (l+ (b- {j} {i} ?a) (b- {j} {i} ?b)))",
                i = &i,
                j = &j
            )
            .parse::<Pattern<Math>>()
            .unwrap()
            .apply_one(egraph, eclass, subst);
            return vec![bind_ij, bind_ji].concat();
        }
        vec![]
    }
}

#[derive(Debug)]
struct RAMul {
    a: Var,
    b: Var,
}

impl Applier<Math, Meta> for RAMul {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<Math, Meta>,
        eclass: egg::Id,
        subst: &egg::Subst,
    ) -> Vec<egg::Id> {
        let a = subst[self.a];
        let b = subst[self.b];
        let mul = egraph.add(Math::Mul([a, b]));
        egraph.rebuild();
        // let mul_meta = &egraph[mul.id].metadata;
        let mul_schema: Vec<String> = egraph[mul]
            .data
            .schema
            .as_ref()
            .unwrap()
            .get_schm()
            .keys()
            .cloned()
            .collect();
        let a_schema: HashSet<_> = egraph[a]
            .data
            .schema
            .as_ref()
            .unwrap()
            .get_schm()
            .keys()
            .filter(|&k| k != "_")
            .collect();
        let b_schema: HashSet<_> = egraph[b]
            .data
            .schema
            .as_ref()
            .unwrap()
            .get_schm()
            .keys()
            .filter(|&k| k != "_")
            .collect();

        let mut res = vec![];
        if mul_schema.len() <= 2 {
            let wc = "_".to_owned();
            let i = mul_schema.get(0).unwrap_or(&wc).clone();
            let j = mul_schema.get(1).unwrap_or(&wc).clone();
            let ai = if let None = a_schema.get(&i) { &wc } else { &i };
            let aj = if let None = a_schema.get(&j) { &wc } else { &j };
            let bi = if let None = b_schema.get(&i) { &wc } else { &i };
            let bj = if let None = b_schema.get(&j) { &wc } else { &j };

            if a_schema.is_subset(&b_schema) || b_schema.is_subset(&a_schema) {
                let bij = format!(
                    "(b+ {i} {j} (l* (b- {ai} {aj} ?a) (b- {bi} {bj} ?b)))",
                    i = &i,
                    j = &j,
                    ai = &ai,
                    aj = &aj,
                    bi = &bi,
                    bj = &bj
                );
                let bind_ij = bij
                    .parse::<Pattern<Math>>()
                    .unwrap()
                    .apply_one(egraph, eclass, subst);

                let bji = format!(
                    "(b+ {j} {i} (l* (b- {aj} {ai} ?a) (b- {bj} {bi} ?b)))",
                    i = &i,
                    j = &j,
                    ai = &ai,
                    aj = &aj,
                    bi = &bi,
                    bj = &bj
                );
                let bind_ji = bji
                    .parse::<Pattern<Math>>()
                    .unwrap()
                    .apply_one(egraph, eclass, subst);
                return vec![bind_ij, bind_ji].concat();
            } else {
                let i = a_schema.into_iter().next().unwrap_or(&wc).clone();
                let j = b_schema.into_iter().next().unwrap_or(&wc).clone();
                return format!(
                    "(b+ {i} {j} (m* (b- {i} _ ?a) (b- _ {j} ?b)))",
                    i = &i,
                    j = &j
                )
                .parse::<Pattern<Math>>()
                .unwrap()
                .apply_one(egraph, eclass, subst);
            }
        }
    }
}

#[derive(Debug)]
struct RABind {
    e: Var,
}

impl Applier<Math, Meta> for RABind {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<Math, Meta>,
        eclass: egg::Id,
        subst: &egg::Subst,
    ) -> Vec<egg::Id> {
        let e = subst[self.e];

        if let Some(Schema::Schm(schema)) = egraph[e].metadata.schema.as_ref() {
            let mut schema = schema.keys();
            if schema.len() <= 2 {
                let wc = "_".to_owned();
                let i = schema.next().unwrap_or(&wc).clone();
                let j = schema.next().unwrap_or(&wc).clone();

                let bind_ij = format!("(b+ {i} {j} (b- {i} {j} ?e))", i = i, j = j)
                    .parse::<Pattern<Math>>()
                    .unwrap()
                    .apply_one(egraph, eclass, subst);

                let bind_ji = format!("(b+ {j} {i} (b- {j} {i} ?e))", i = i, j = j)
                    .parse::<Pattern<Math>>()
                    .unwrap()
                    .apply_one(egraph, eclass, subst);
                return vec![bind_ij, bind_ji].concat();
            }
        }
        vec![]
    }
}

#[derive(Debug)]
struct RARMMul {
    a: Var,
    b: Var,
}

impl Applier<Math, Meta> for RARMMul {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<Math, Meta>,
        eclass: egg::Id,
        subst: &egg::Subst,
    ) -> Vec<egg::Id> {
        let a = subst[self.a];
        let b = subst[self.b];
        let mul = egraph.add(Math::RMMul([a, b]));
        let mul_schema: HashSet<_> = egraph[mul]
            .data
            .schema
            .as_ref()
            .unwrap()
            .get_schm()
            .keys()
            .collect();
        let a_schema: HashSet<_> = egraph[a]
            .data
            .schema
            .as_ref()
            .unwrap()
            .get_schm()
            .keys()
            .collect();
        let b_schema: HashSet<_> = egraph[b]
            .data
            .schema
            .as_ref()
            .unwrap()
            .get_schm()
            .keys()
            .collect();

        let wc = "_".to_owned();
        let i = a_schema
            .difference(&b_schema)
            .cloned()
            .next()
            .unwrap_or(&wc)
            .clone();
        let k = b_schema
            .difference(&a_schema)
            .cloned()
            .next()
            .unwrap_or(&wc)
            .clone();
        let j = a_schema
            .difference(&mul_schema)
            .cloned()
            .next()
            .unwrap_or(&wc)
            .clone();

        // let mut res = vec![];
        // let mut bind_ik = Math::parse_pattern(&)
        // .unwrap()
        // .apply(egraph, map);
        // res.append(&mut bind_ik);

        // let mut res = vec![];
        format!(
            "(b+ {k} {i} (m* (b- {k} {j} ?b) (b- {j} {i} ?a)))",
            i = &i,
            j = &j,
            k = &k
        )
        .parse::<Pattern<Math>>()
        .unwrap()
        .apply_one(egraph, eclass, subst)
    }
}

#[derive(Debug)]
struct RASum {
    i: Var,
    x: Var,
}

impl Applier<Math, Meta> for RASum {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<Math, Meta>,
        eclass: egg::Id,
        subst: &egg::Subst,
    ) -> Vec<egg::Id> {
        let i = subst[self.i];
        let x = subst[self.x];
        let i_s = egraph[i].data.schema.as_ref().unwrap().get_dims().0.clone();
        let sum = egraph.add(Math::Agg([i, x]));
        let mut schema = egraph[sum].data.schema.as_ref().unwrap().get_schm().keys();

        if schema.len() <= 1 {
            let wc = "_".to_owned();
            let j = schema.next().unwrap_or(&wc).clone();

            let scol = format!("(b+ _ {j} (scol (b- {i} {j} ?x)))", j = &j, i = &i_s)
                .parse::<Pattern<Math>>()
                .unwrap()
                .apply_one(egraph, eclass, subst);

            let srow = format!("(b+ {j} _ (srow (b- {j} {i} ?x)))", j = &j, i = &i_s)
                .parse::<Pattern<Math>>()
                .unwrap()
                .apply_one(egraph, eclass, subst);
            return vec![scol, srow].concat();
        }
        vec![]
    }
}
