//! Ternary decision diagrams (TDDs)

cfg_if::cfg_if! {
    if #[cfg(feature = "manager-pointer")] {
        pub use pointer::{QDDFunction, QDDManagerRef};
    } else if #[cfg(feature = "manager-index")] {
        pub use index::{QDDFunction, QDDManagerRef};
    } else {
        pub type QDDFunction = ();
        pub type QDDManagerRef = ();
    }
}

/// Create a new manager for a simple binary decision diagram
#[allow(unused_variables)]
pub fn new_manager(
    inner_node_capacity: usize,
    apply_cache_capacity: usize,
    threads: u32,
) -> QDDManagerRef {
    cfg_if::cfg_if! {
        if #[cfg(feature = "manager-pointer")] {
            pointer::QDDManagerRef::new_manager(inner_node_capacity, apply_cache_capacity, threads)
        } else if #[cfg(feature = "manager-index")] {
            index::QDDManagerRef::new_manager(inner_node_capacity, 3, apply_cache_capacity, threads)
        } else {
            unreachable!()
        }
    }
}

/// Print statistics to stderr
pub fn print_stats() {
    #[cfg(not(feature = "statistics"))]
    eprintln!("[statistics feature disabled]");

    #[cfg(feature = "statistics")]
    oxidd_rules_tdd::print_stats();
}

#[cfg(all(feature = "manager-index", not(feature = "manager-pointer")))]
mod index {
    use oxidd_manager_index::node::fixed_arity::NodeWithLevelCons;
    use oxidd_manager_index::terminal_manager::StaticTerminalManagerCons;
    use oxidd_rules_qdd::QDDOp;
    use oxidd_rules_qdd::QDDRules;
    use oxidd_rules_qdd::QDDTerminal;

    use crate::util::type_cons::DD;

    crate::util::dd_index_based!(QDD {
        node: NodeWithLevelCons<3>,
        edge_tag: (),
        terminal_manager: StaticTerminalManagerCons<QDDTerminal>,
        rules: QDDRulesCons for QDDRules,
        manager_data: QDDManagerDataCons for QDDManagerData,
        terminals: 2,
    });

    crate::util::manager_data!(QDDManagerData for QDD, operator: QDDOp, cache_max_arity: 2);

    crate::util::manager_ref_index_based!(pub struct QDDManagerRef(<QDD as DD>::ManagerRef) with QDDManagerData);

    //#[cfg(not(feature = "multi-threading"))]
    type FunctionInner = oxidd_rules_qdd::QDDFunction<<QDD as DD>::Function>;
    //#[cfg(feature = "multi-threading")]
    //type FunctionInner = oxidd_rules_tdd::TDDFunctionMT<<TDD as DD>::Function>;

    #[derive(
        Clone,
        PartialEq,
        Eq,
        PartialOrd,
        Ord,
        Hash,
        oxidd_derive::Function,
        oxidd_derive::BooleanFunction,
    )]
    #[use_manager_ref(QDDManagerRef, QDDManagerRef(inner))]
    pub struct QDDFunction(FunctionInner);
    crate::util::derive_raw_function_index_based!(for: QDDFunction, inner: FunctionInner);

    impl oxidd_dump::dot::DotStyle<()> for QDDFunction {
        fn edge_style(
            no: usize,
            tag: (),
        ) -> (oxidd_dump::dot::EdgeStyle, bool, oxidd_dump::dot::Color) {
            FunctionInner::edge_style(no, tag)
        }
    }
}

#[cfg(feature = "manager-pointer")]
mod pointer {
    use oxidd_manager_pointer::node::fixed_arity::NodeWithLevelCons;
    use oxidd_manager_pointer::terminal_manager::StaticTerminalManagerCons;
    use oxidd_rules_tdd::QDDOp;
    use oxidd_rules_tdd::QDDRules;
    use oxidd_rules_tdd::QDDTerminal;

    use crate::util::type_cons::DD;

    crate::util::dd_pointer_based!(QDD {
        node: NodeWithLevelCons<3>,
        edge_tag: (),
        terminal_manager: StaticTerminalManagerCons<QDDTerminal>,
        rules: QDDRulesCons for QDDRules,
        manager_data: QDDManagerDataCons for QDDManagerData,
        tag_bits: 1,
    });

    crate::util::manager_data!(QDDManagerData for QDD, operator: QDDOp, cache_max_arity: 2);

    crate::util::manager_ref_pointer_based!(pub struct QDDManagerRef(<QDD as DD>::ManagerRef) with QDDManagerData);

    //#[cfg(not(feature = "multi-threading"))]
    type FunctionInner = oxidd_rules_tdd::QDDFunction<<QDD as DD>::Function>;
    //#[cfg(feature = "multi-threading")]
    //type FunctionInner = oxidd_rules_tdd::TDDFunctionMT<<TDD as DD>::Function>;

    #[derive(
        Clone,
        PartialEq,
        Eq,
        PartialOrd,
        Ord,
        Hash,
        oxidd_derive::Function,
        oxidd_derive::BooleanFunction,
    )]
    #[use_manager_ref(QDDManagerRef)]
    pub struct QDDFunction(FunctionInner);
    crate::util::derive_raw_function_pointer_based!(for: QDDFunction, inner: FunctionInner);

    impl oxidd_dump::dot::DotStyle<()> for QDDFunction {
        fn edge_style(
            no: usize,
            tag: (),
        ) -> (oxidd_dump::dot::EdgeStyle, bool, oxidd_dump::dot::Color) {
            FunctionInner::edge_style(no, tag)
        }
    }
}

#[cfg(test)]
mod tests {
    use oxidd_core::{function::BooleanFunction, util::AllocResult, ManagerRef};

    use super::*;
    use oxidd_dump::{dddmp, dot::dump_all};

    #[test]
    fn construct() -> AllocResult<()> {
        let manager_ref = new_manager(2048, 1024, 8);

        let (x1, x2, x3) = manager_ref.with_manager_exclusive(|manager| {
            (
                QDDFunction::new_var(manager).unwrap(),
                QDDFunction::new_var(manager).unwrap(),
                QDDFunction::new_var(manager).unwrap(),
            )
        });

        let f = x1.and(&x2.or(&x3)?)?;

        // manager_ref.with_manager_shared(|manager| {
        //     let file = std::fs::File::create(
        //         "C:\\Users\\tarva\\Documents\\Projects\\Github\\oxidd-fork\\data\\qdd.dot",
        //     )
        //     .expect("could not create `qdd.dot`");
        //     dump_all(
        //         file,
        //         manager,
        //         [(&x1, "x1"), (&x2, "x2"), (&x3, "x3")],
        //         [(&f, "x1 && (x2 || x3)")],
        //     )
        //     .expect("dot export failed");
        // });

        manager_ref.with_manager_shared(|manager| {
            let file = std::fs::File::create(
                "C:\\Users\\tarva\\Documents\\Projects\\Github\\oxidd-fork\\data\\qdd.dddmp",
            )
            .expect("could not create `qdd.dddmp`");

            dddmp::export(
                file,
                manager,
                true,
                "qdd",
                &[&x1, &x2, &x3],
                Some(&["x1", "x2", "x3"]),
                &[&f],
                Some(&["f"]),
                |e| false,
            )
            .expect("export failed");
        });

        Ok(())
    }
}
