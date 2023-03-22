use std::{
    collections::{HashMap, HashSet},
    time::Instant,
};

use egg::{Analysis, EGraph, Id, Language, RecExpr};
use rand::Rng;

pub mod ILPExtract {
    use super::*;
    use rplex::{self, var, Problem, VariableValue, WeightedVariable};

    fn get_all_cycles<'a, L, N>(
        egraph: &EGraph<L, N>,
        root: &Id,
        color: &mut HashMap<Id, usize>,
        path: &mut Vec<(Id, L)>,
        problem: &mut Problem<'a>,
        node_vars: &HashMap<L, usize>,
        // node_to_children: &HashMap<usize, HashSet<Id>>,
    ) where
        L: Language,
        N: Analysis<L>,
    {
        if color.contains_key(root) && color[root] == 2 {
            return;
        }
        if color.contains_key(root) && color[root] == 1 {
            if let Some((idx, _)) = path.iter().enumerate().find(|(_, (id, _))| id == root) {
                let mut new_cycle = Vec::new();
                let subpath = path[idx..].to_vec();
                for (_, n) in &subpath {
                    new_cycle.push(node_vars[n]);
                }
                let mut rng = rand::thread_rng();
                if new_cycle.len() == 1 {
                    let mut constraint = rplex::Constraint::new(
                        rplex::ConstraintType::Eq,
                        0.0,
                        format!("cycle_{}_{}", root, rng.gen::<u64>()),
                    );
                    constraint.add_wvar(WeightedVariable::new_idx(new_cycle[0], 1.0));
                    problem.add_constraint(constraint).unwrap();
                } else {
                    let nxt_hop = subpath[1].0;
                    for node_idx in egraph[*root].nodes.iter().map(|n| node_vars[n]) {
                        // if node_to_children[&node_idx].contains(&nxt_hop) {
                        new_cycle[0] = node_idx;
                        // sum up <= len(new_cycle) - 1
                        let mut constraint = rplex::Constraint::new(
                            rplex::ConstraintType::LessThanEq,
                            new_cycle.len() as f64 - 1.0,
                            format!("cycle_{}_{}", root, rng.gen::<u64>()),
                        );
                        for node_idx in new_cycle.iter() {
                            constraint.add_wvar(WeightedVariable::new_idx(*node_idx, 1.0));
                        }
                        problem.add_constraint(constraint).unwrap();
                        // }
                    }
                }
                return;
            }
            panic!("Should have a cycle here: {}; path: {:?}", root, path);
        }
        color.insert(*root, 1);
        for node in egraph[*root].nodes.iter() {
            path.push((*root, node.clone()));
            for ch in node.children() {
                get_all_cycles(
                    egraph, ch, color, path, problem, node_vars,
                    // node_to_children,
                );
            }
            path.pop();
        }
        color.insert(*root, 2);
    }

    pub struct ILPProblem<'a, L, N>
    where
        L: Language,
        N: Analysis<L>,
    {
        pub node_vars: HashMap<L, usize>,
        pub problem: Problem<'a>,
        pub root: Id,
        pub egraph: &'a EGraph<L, N>,
    }

    impl<'a, L, N> ILPProblem<'a, L, N>
    where
        L: Language,
        N: Analysis<L>,
    {
        pub fn new(
            problem: Problem<'a>,
            egraph: &'a EGraph<L, N>,
            root: Id,
            node_vars: HashMap<L, usize>,
        ) -> Self {
            ILPProblem {
                problem,
                root,
                node_vars,
                egraph,
            }
        }

        pub fn solve(&mut self) -> (u128, f64, RecExpr<L>) {
            self.problem
                .set_objective_type(rplex::ObjectiveType::Minimize)
                .unwrap();
            let start = Instant::now();
            let solution = self.problem.solve().unwrap();
            let solve_time = start.elapsed().as_millis();
            let cost = solution.objective;

            let mut expr = RecExpr::default();
            let mut new_id_map = HashMap::new();
            let mut worklist = vec![self.root];
            let mut path: Vec<(Id, L)> = Vec::new();

            while let Some(&id) = worklist.last() {
                if new_id_map.contains_key(&id) {
                    worklist.pop();
                    path = path
                        .iter()
                        .cloned()
                        .filter(|(i, _)| *i != id)
                        .collect::<Vec<_>>();
                    continue;
                }
                let mut not_found = true;
                for node in &self.egraph[id].nodes {
                    let node_idx = self.node_vars[node];
                    match solution.variables[node_idx] {
                        VariableValue::Binary(true) => {
                            path.push((id, node.clone()));
                            not_found = false;
                            if node.all(|c| new_id_map.contains_key(&c)) {
                                let new_id =
                                    expr.add(node.clone().map_children(|c| new_id_map[&c]));
                                new_id_map.insert(id, new_id);
                                path = path
                                    .iter()
                                    .cloned()
                                    .filter(|(i, _)| *i != id)
                                    .collect::<Vec<_>>();
                                worklist.pop();
                            } else {
                                let pending_work = node
                                    .children()
                                    .iter()
                                    .filter(|&x| !new_id_map.contains_key(x))
                                    .collect::<Vec<_>>();
                                for each in pending_work {
                                    if let Some((idx, _)) =
                                        path.iter().enumerate().find(|(_, (id, _))| id == each)
                                    {
                                        let subpath = path[idx..]
                                            .iter()
                                            .map(|(_, l)| l.clone())
                                            .collect::<Vec<_>>();
                                        panic!("Cycle detected at {}: {:?}", id, subpath);
                                    }
                                }
                                worklist.extend(node.children());
                            }
                            break;
                        }
                        _ => continue,
                    }
                }
                if not_found {
                    panic!("No enode chosen for eclass {}", id);
                }
            }

            return (solve_time, cost, expr);
        }
    }

    fn node_name(idx: usize) -> String {
        format!("node_idx_{}", idx)
    }

    pub fn create_problem<'a, L, N, CF>(
        env: &'a rplex::Env,
        root: Id,
        egraph: &'a EGraph<L, N>,
        no_cycle: bool,
        topo_sort: bool,
        mut cost_fn: CF,
    ) -> ILPProblem<'a, L, N>
    where
        L: Language,
        N: Analysis<L>,
        CF: FnMut(&EGraph<L, N>, egg::Id, &L) -> f64,
    {
        let mut problem = Problem::new(&env, "egraph_ext").unwrap();
        let mut node_vars = HashMap::new();

        // create node_vars
        for eclass in egraph.classes() {
            for (idx, node) in eclass.nodes.iter().enumerate() {
                let name = node_name(idx);
                let cost = cost_fn(egraph, eclass.id, node);
                let var = var!(0.0 <= name <= 1.0 -> cost as Binary);
                node_vars.insert(node.clone(), problem.add_variable(var).unwrap());
            }
        }

        // root constraint
        let mut constraint =
            rplex::Constraint::new(rplex::ConstraintType::Eq, 1.0, "root constraint");
        for node_idx in egraph[root].nodes.iter().map(|x| node_vars[x]) {
            constraint.add_wvar(WeightedVariable::new_idx(node_idx, 1.0));
        }
        problem.add_constraint(constraint).unwrap();
        // let mut node_to_children = HashMap::new();

        // children constraint
        for eclass in egraph.classes() {
            for node in egraph[eclass.id].nodes.iter() {
                let node_idx = node_vars[node];
                // let mut node_children_set = HashSet::new();
                for (ch_idx, ch) in node.children().iter().enumerate() {
                    // node_children_set.insert(*ch);
                    let mut constraint = rplex::Constraint::new(
                        rplex::ConstraintType::GreaterThanEq,
                        0.0,
                        format!("{}_child_{}", node_idx, ch_idx),
                    );
                    constraint.add_wvar(WeightedVariable::new_idx(node_idx, -1.0));
                    for ch_node_idx in egraph[*ch].nodes.iter().map(|x| node_vars[x]) {
                        constraint.add_wvar(WeightedVariable::new_idx(ch_node_idx, 1.0));
                    }
                    problem.add_constraint(constraint).unwrap();
                }
                // node_to_children.insert(node_idx, node_children_set);
            }
        }

        if no_cycle {
            if topo_sort {
                // add topo variables for each enode
                let mut topo_vars = HashMap::new();
                let top = egraph.total_size() as f64;
                for eclass in egraph.classes() {
                    let name = format!("topo_{}", eclass.id);
                    let var = var!(0.0 <= name <= (top - 1.0) -> 0.0 as Integer);
                    topo_vars.insert(eclass.id, problem.add_variable(var).unwrap());
                }
                // topolotical ordering
                for eclass in egraph.classes() {
                    for enode in eclass.nodes.iter() {
                        for child in enode.children().iter() {
                            let mut topo_constraint = rplex::Constraint::new(
                                rplex::ConstraintType::GreaterThanEq,
                                1.0 - top,
                                format!("topo_sort_{}_{}", eclass.id, child),
                            );
                            topo_constraint
                                .add_wvar(WeightedVariable::new_idx(topo_vars[&eclass.id], 1.0));
                            topo_constraint
                                .add_wvar(WeightedVariable::new_idx(node_vars[enode], -top));
                            topo_constraint
                                .add_wvar(WeightedVariable::new_idx(topo_vars[child], -1.0));
                            problem.add_constraint(topo_constraint).unwrap();
                        }
                    }
                }
            } else {
                let mut color = HashMap::new();
                let mut path = Vec::new();
                get_all_cycles(
                    egraph,
                    &root,
                    &mut color,
                    &mut path,
                    &mut problem,
                    &node_vars,
                    // &node_to_children,
                );
            }
        }

        return ILPProblem::new(problem, egraph, root, node_vars);
    }
}

pub mod MaxSATExtract {
    use super::*;
    use std::process::Command;
    use std::time::Instant;

    fn disjuct_negative(nodes: &Vec<usize>, problem_writer: &mut ProblemWriter, top: f64) {
        let clause = nodes
            .iter()
            .map(|x| format!("-{}", x))
            .collect::<Vec<_>>()
            .join(" ");
        problem_writer.hard_clause(&clause, top);
    }

    fn get_all_cycles<L, N>(
        egraph: &EGraph<L, N>,
        root: &Id,
        color: &mut HashMap<Id, usize>,
        path: &mut Vec<(Id, L)>,
        problem_writer: &mut ProblemWriter,
        node_vars: &HashMap<L, usize>,
        node_to_children: &HashMap<usize, HashSet<Id>>,
        top: f64,
    ) where
        L: Language,
        N: Analysis<L>,
    {
        if color.contains_key(root) && color[root] == 2 {
            return;
        }
        if color.contains_key(root) && color[root] == 1 {
            if let Some((idx, _)) = path.iter().enumerate().find(|(_, (id, _))| id == root) {
                let mut new_cycle = Vec::new();
                let subpath = path[idx..].to_vec();
                for (_, n) in &subpath {
                    new_cycle.push(node_vars[&n]);
                }
                if new_cycle.len() == 1 {
                    problem_writer.hard_clause(&format!("-{}", new_cycle[0]), top);
                } else {
                    let nxt_hop = subpath[1].0;
                    for node_idx in egraph[*root].nodes.iter().map(|x| node_vars[x]) {
                        // if node_to_children[&node_idx].contains(&nxt_hop) {
                        new_cycle[0] = node_idx;
                        disjuct_negative(&new_cycle, problem_writer, top);
                        // }
                    }
                }
                return;
            }
            panic!("Should have a cycle here: {}; path: {:?}", root, path);
        }
        color.insert(*root, 1);
        for node in egraph[*root].nodes.iter() {
            for ch in node.children() {
                // let mut to_here = path.clone();
                // to_here.push((*root, node.clone()));
                path.push((*root, node.clone()));
                get_all_cycles(
                    egraph,
                    ch,
                    color,
                    path,
                    problem_writer,
                    node_vars,
                    node_to_children,
                    top,
                );
                path.pop();
            }
        }
        color.insert(*root, 2);
    }

    #[derive(Clone)]
    struct ProblemWriter {
        pub path: String,
        problem: String,
        parameters: String,
        clause_counter: usize,
    }

    impl ProblemWriter {
        pub fn new(path: String) -> Self {
            Self {
                path,
                problem: String::new(),
                parameters: String::new(),
                clause_counter: 0,
            }
        }

        pub fn comment(&mut self, comment: &str) {
            self.problem.push_str(&format!("c {}\n", comment));
        }

        pub fn parameters(&mut self, num_vars: usize, top: f64) {
            self.parameters = format!(
                "p wcnf {} {} {}\n",
                num_vars, self.clause_counter, top as i64
            );
        }

        pub fn hard_clause(&mut self, clause: &str, top: f64) {
            self.clause_counter += 1;
            self.problem
                .push_str(&format!("{} {} 0\n", top as i64, clause));
        }

        pub fn soft_clause(&mut self, clause: &str, weight: f64) {
            self.clause_counter += 1;
            self.problem
                .push_str(&format!("{} {} 0\n", weight as i64, clause));
        }

        pub fn dump(&mut self) {
            println!("written to {}", self.path);
            std::fs::write(
                self.path.clone(),
                format!("{}{}", self.parameters.clone(), self.problem.clone()),
            )
            .unwrap();
        }
    }

    /// the Extractor that constructs the constraint problem
    pub struct MaxsatExtractor<'a, L: Language, N: Analysis<L>> {
        /// EGraph to extract
        pub egraph: &'a EGraph<L, N>,
        writer: ProblemWriter,
    }

    /// A weighted partial maxsat problem
    pub struct WeightedPartialMaxsatProblem<'a, L: Language, N: Analysis<L>> {
        // pub class_vars: HashMap<Id, i32>,
        /// a map from enodes to maxsat variables (starting from 1)
        pub node_vars: HashMap<L, usize>,
        /// root eclass Id
        pub root: Id,
        /// EGraph to extract
        pub egraph: &'a EGraph<L, N>,
        top: f64,
        problem_writer: ProblemWriter,
    }

    impl<'a, L, N> WeightedPartialMaxsatProblem<'a, L, N>
    where
        L: Language,
        N: Analysis<L>,
    {
        /// Given a weighted partial maxsat problem, solve the problem
        /// and parse the output
        pub fn solve(&self) -> Result<(u128, Option<f64>, RecExpr<L>), (u128, Vec<usize>)> {
            // assume maxhs installed
            let start = Instant::now();
            let result = Command::new("maxhs")
                .arg("-printSoln")
                .arg(self.problem_writer.path.clone())
                .output();
            let elapsed = start.elapsed().as_millis();
            if let Ok(output) = result {
                let stdout = String::from_utf8_lossy(&output.stdout);
                let lines = stdout.lines();
                let (mut comments, mut opt_line, mut sol_line, mut solution) =
                    (vec![], vec![], vec![], vec![]);
                for l in lines {
                    let mut line = l.split(" ");
                    if let Some(indicator) = line.next() {
                        match indicator {
                            "c" => comments.push(line.collect::<Vec<_>>().join(" ")),
                            "o" => opt_line.push(line.collect::<Vec<_>>().join(" ")),
                            "s" => sol_line.push(line.collect::<Vec<_>>().join(" ")),
                            "v" => solution.push(line.collect::<Vec<_>>().join(" ")),
                            _ => (),
                        }
                    }
                }
                assert!(sol_line.len() > 0, "Solution cannot be empty");
                let sol = sol_line.iter().next().unwrap();
                if sol.contains("UNSATISFIABLE") {
                    panic!("Problem UNSAT")
                } else {
                    assert!(
                        solution.len() > 0,
                        "No solution line (try add -printSoln option to maxhs)"
                    );
                    let sol = solution.iter().next().unwrap();
                    // println!("Sol: {}", sol);
                    let sat_map = sol
                        .chars()
                        .enumerate()
                        .filter(|(_, res)| *res == '1')
                        .map(|(car, _)| car + 1)
                        .collect::<HashSet<_>>();
                    let mut worklist = Vec::new();
                    let mut expr = RecExpr::default();
                    let mut id_map = HashMap::new();
                    worklist.push(self.root);
                    let mut path: Vec<(Id, L)> = Vec::new();
                    while let Some(&id) = worklist.last() {
                        if id_map.contains_key(&id) {
                            worklist.pop();
                            path = path
                                .iter()
                                .cloned()
                                .filter(|(i, _)| *i != id)
                                .collect::<Vec<_>>();
                            continue;
                        }
                        // println!("Current node ids: {:?}", &self.egraph[id].nodes.iter().map(|x| self.node_vars[x]).collect::<Vec<_>>());
                        let mut not_found = true;
                        for n in &self.egraph[id].nodes {
                            if sat_map.contains(&self.node_vars[&n]) {
                                path.push((id, n.clone()));
                                not_found = false;
                                if n.all(|ch| id_map.contains_key(&ch)) {
                                    let new_id = expr.add(
                                        n.clone().map_children(|ch| id_map[&self.egraph.find(ch)]),
                                    );
                                    id_map.insert(id.clone(), new_id);
                                    path = path
                                        .iter()
                                        .cloned()
                                        .filter(|(i, _)| *i != id)
                                        .collect::<Vec<_>>();
                                    worklist.pop();
                                } else {
                                    let pending_work = n
                                        .children()
                                        .iter()
                                        .filter(|&x| !id_map.contains_key(x))
                                        .collect::<Vec<_>>();
                                    for each in pending_work {
                                        if let Some((idx, _)) =
                                            path.iter().enumerate().find(|(_, (id, _))| id == each)
                                        {
                                            let subpath = path[idx..]
                                                .iter()
                                                .map(|(_, l)| l.clone())
                                                .collect::<Vec<_>>();
                                            return Err((
                                                elapsed,
                                                subpath
                                                    .iter()
                                                    .map(|x| self.node_vars[x])
                                                    .collect::<Vec<_>>(),
                                            ));
                                        }
                                    }
                                    worklist.extend_from_slice(n.children());
                                }
                                break;
                            }
                        }
                        if not_found {
                            panic!("No active node for eclass: {}", id.clone());
                        }
                    }
                    // parse opt
                    if opt_line.len() > 0 {
                        let opt = opt_line.iter().next().unwrap();
                        return Ok((elapsed, Some(opt.parse::<f64>().unwrap()), expr));
                    }
                    return Ok((elapsed, None, expr));
                }
            } else {
                panic!(
                    "Unable to solve {}, err: {}",
                    self.problem_writer.path,
                    result.err().unwrap()
                );
            }
        }

        pub fn solve_with_refinement(&mut self) -> (u128, Option<f64>, RecExpr<L>) {
            let mut total_time = 0;
            loop {
                let x = self.solve();
                if x.is_err() {
                    let (t, cycle) = x.err().unwrap();
                    total_time += t;
                    println!("Elim Cycle: {:?}", cycle);
                    let cycle_elim_clause = cycle
                        .iter()
                        .map(|x| format!("-{}", x))
                        .collect::<Vec<_>>()
                        .join(" ");
                    self.problem_writer
                        .hard_clause(&cycle_elim_clause, self.top);
                    self.problem_writer
                        .parameters(self.node_vars.len(), self.top);
                    self.problem_writer.dump();
                } else {
                    let (t1, x, y) = x.unwrap();
                    return (t1 + total_time, x, y);
                }
            }
        }
    }

    /// Cost function; same interface as `LpCostFunction`.
    pub trait MaxsatCostFunction<L: Language, N: Analysis<L>> {
        /// Returns the cost of the given e-node.
        ///
        /// This function may look at other parts of the e-graph to compute the cost
        /// of the given e-node.
        fn node_cost(&mut self, egraph: &EGraph<L, N>, eclass: Id, enode: &L) -> f64;
    }

    impl<'a, L, N> MaxsatExtractor<'a, L, N>
    where
        L: Language,
        N: Analysis<L>,
    {
        /// create a new maxsat extractor
        pub fn new(egraph: &'a EGraph<L, N>, path: String) -> Self {
            Self {
                egraph,
                writer: ProblemWriter::new(path.clone()),
            }
        }

        /// create a maxsat problem
        pub fn create_problem<CF>(
            &mut self,
            root: Id,
            name: &str,
            no_cycle: bool,
            mut cost_fn: CF,
        ) -> WeightedPartialMaxsatProblem<'a, L, N>
        where
            CF: MaxsatCostFunction<L, N>,
        {
            // Hard Constraints
            // === root constraint (pick at least one in root)
            // \forall n \in R, \bigvee v_n
            // === children constraint
            // \forall n, \forall C\in children(n), v_n -> \bigvee_cN v_cN \forall cN \in C
            self.writer.comment(&format!("Problem: {}", name));
            // create variables
            let mut num_vars = 0;
            let mut top = 0 as f64;
            let mut node_vars = HashMap::default();
            let mut node_weight_map = HashMap::new();
            for c in self.egraph.classes() {
                for n in c.nodes.iter() {
                    node_vars.insert(n.clone(), num_vars + 1);
                    num_vars += 1;

                    node_weight_map.insert(n.clone(), cost_fn.node_cost(self.egraph, c.id, n));
                    top += cost_fn.node_cost(self.egraph, c.id, n);
                }
            }

            let top = top + 1 as f64;

            // Hard clauses
            let mut hard_clauses = Vec::new();
            // root constraint
            let root_clause = self.egraph[root]
                .nodes
                .iter()
                .map(|n| node_vars[n])
                .map(|v| v.to_string())
                .collect::<Vec<_>>()
                .join(" ");
            hard_clauses.push(root_clause);

            let mut node_to_children = HashMap::new();
            // children constraint
            for c in self.egraph.classes() {
                for n in c.nodes.iter() {
                    // v_n -> \bigvee_cN v_cN forall C
                    let mut node_children = HashSet::new();
                    for ch in n.children() {
                        node_children.insert(*ch);
                        let mut clause = String::new();
                        clause.push_str(&format!("-{}", node_vars[n]));
                        for ch_node in self.egraph[*ch].nodes.iter() {
                            clause.push_str(&format!(" {}", node_vars[ch_node]));
                        }
                        hard_clauses.push(clause);
                    }
                    node_to_children.insert(node_vars[n], node_children);
                }
            }

            // cycle constraint
            if no_cycle {
                // let mut cycles = HashMap::new();
                let mut path = Vec::new();
                get_all_cycles(
                    self.egraph,
                    &root,
                    &mut HashMap::new(),
                    &mut path,
                    &mut self.writer,
                    &node_vars,
                    &node_to_children,
                    top,
                );
            }

            // soft clauses (i.e. not all nodes need to be picked)
            let mut soft_clauses = HashMap::new();
            for c in self.egraph.classes() {
                for n in c.nodes.iter() {
                    soft_clauses.insert(n.clone(), format!("-{}", node_vars[n]));
                }
            }

            let nbvars = num_vars;

            self.writer.comment("Hard clauses:");
            for clause in hard_clauses {
                self.writer.hard_clause(&clause, top);
            }

            self.writer.comment("Soft clauses:");
            for (n, clause) in soft_clauses {
                self.writer.soft_clause(&clause, node_weight_map[&n]);
            }

            self.writer.parameters(nbvars, top);

            self.writer.dump();

            WeightedPartialMaxsatProblem {
                top,
                node_vars,
                root,
                egraph: self.egraph,
                problem_writer: self.writer.clone(),
            }
        }
    }
}
