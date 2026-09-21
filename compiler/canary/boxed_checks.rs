//! Executable checks of generated code with deferred, instrumented inputs.
#![allow(dead_code)]

mod local_lazy {
    include!(concat!(env!("H2R_CANARY_DIR"), "/localLazy.rs"));
    #[test]
    fn recursive_local_calls_preserve_lazy_captures_and_arguments() {
        let poison = HInt::defer(|| panic!("unused recursive argument forced"));
        let count = std::rc::Rc::new(std::cell::Cell::new(0));
        let counter = count.clone();
        let input = HInt::defer(move || {
            counter.set(counter.get() + 1);
            42
        });
        let result = h2r_entry(input, poison.clone());
        assert_eq!(count.get(), 0);
        assert_eq!(result.force(), 42);
        assert_eq!(result.force(), 42);
        assert_eq!(count.get(), 1);
        assert!(!poison.is_evaluated());
    }
}

mod data_lazy {
    include!(concat!(env!("H2R_CANARY_DIR"), "/dataLazy.rs"));
    #[test]
    fn matching_product_does_not_force_unused_computed_field() {
        let poison = HInt::defer(|| panic!("unused constructor field forced"));
        let result = h2r_entry(HInt::ready(42), poison.clone());
        assert!(!result.is_evaluated());
        assert_eq!(result.force(), 42);
        assert!(!poison.is_evaluated());
    }
}

mod data_nested {
    include!(concat!(env!("H2R_CANARY_DIR"), "/dataNested.rs"));
    #[test]
    fn nested_patterns_only_force_selected_fields() {
        let poison = HInt::defer(|| panic!("unselected nested field forced"));
        assert_eq!(h2r_entry(HInt::ready(7), poison.clone()).force(), 7);
        assert!(!poison.is_evaluated());
    }
}

mod data_strict {
    include!(concat!(env!("H2R_CANARY_DIR"), "/dataStrict.rs"));
    #[test]
    fn strict_field_forced_at_constructor_demand_not_function_call() {
        let x = HInt::defer(|| 13);
        let result = h2r_entry(x.clone(), HInt::ready(42));
        assert!(!x.is_evaluated());
        assert_eq!(result.force(), 42);
        assert!(x.is_evaluated());
    }
}

mod data_list {
    include!(concat!(env!("H2R_CANARY_DIR"), "/dataList.rs"));
    #[test]
    fn list_head_does_not_force_tail_elements() {
        let poison = HInt::defer(|| panic!("tail element forced"));
        assert_eq!(h2r_entry(HInt::ready(42), poison.clone()).force(), 42);
        assert!(!poison.is_evaluated());
    }
}

mod data_default {
    include!(concat!(env!("H2R_CANARY_DIR"), "/dataDefault.rs"));
    #[test]
    fn default_arm_does_not_force_discarded_fields() {
        let poison = HInt::defer(|| panic!("discarded alternative field forced"));
        assert_eq!(h2r_entry(HInt::ready(1), poison.clone()).force(), 0);
        assert!(!poison.is_evaluated());
    }
}

mod ignored {
    include!(concat!(env!("H2R_CANARY_DIR"), "/boxedIgnore.rs"));
    #[test]
    fn unused_argument_is_not_forced() {
        let poison = HInt::defer(|| panic!("unused argument forced"));
        let result = h2r_entry(HInt::ready(42), poison.clone());
        assert!(!result.is_evaluated());
        assert_eq!(result.force(), 42);
        assert!(!poison.is_evaluated());
    }
}

mod sum {
    include!(concat!(env!("H2R_CANARY_DIR"), "/boxedSum.rs"));
    #[test]
    fn calls_are_delayed_and_shared_inputs_evaluate_once() {
        let calls = std::rc::Rc::new(std::cell::Cell::new(0));
        let counter = calls.clone();
        let input = HInt::defer(move || {
            counter.set(counter.get() + 1);
            21
        });
        let result = h2r_entry(input.clone(), input.clone());
        assert_eq!(calls.get(), 0);
        assert!(!input.is_evaluated());
        assert_eq!(result.force(), 42);
        assert_eq!(result.clone().force(), 42);
        assert_eq!(calls.get(), 1);
    }
}

mod choose {
    include!(concat!(env!("H2R_CANARY_DIR"), "/boxedChoose.rs"));
    #[test]
    fn unselected_boxed_branch_is_not_forced() {
        let poison = HInt::defer(|| panic!("unselected branch forced"));
        assert_eq!(h2r_entry(HInt::ready(7), poison.clone()).force(), 7);
        assert!(!poison.is_evaluated());
        assert_eq!(h2r_entry(HInt::ready(0), HInt::ready(9)).force(), 9);
    }
}

mod strict {
    include!(concat!(env!("H2R_CANARY_DIR"), "/boxedStrictIgnore.rs"));
    #[test]
    fn constructor_case_forces_even_an_unused_field() {
        let input = HInt::defer(|| 5);
        let result = h2r_entry(input.clone(), HInt::ready(9));
        assert!(!input.is_evaluated());
        assert_eq!(result.force(), 9);
        assert!(input.is_evaluated());
    }
}

mod caf {
    include!(concat!(env!("H2R_CANARY_DIR"), "/boxedCaf.rs"));
    #[test]
    fn top_level_references_share_the_same_cell() {
        let first = h2r_entry();
        let second = h2r_entry();
        assert!(first.shares_with(&second));
        assert!(!first.is_evaluated());
        assert_eq!(first.force(), 42);
        assert!(second.is_evaluated());
    }
}

mod lazy_argument {
    include!(concat!(env!("H2R_CANARY_DIR"), "/lazyArgument.rs"));
    #[test]
    fn computed_unused_argument_stays_unevaluated() {
        let poison = HInt::defer(|| panic!("computed unused argument forced"));
        assert_eq!(h2r_entry(HInt::ready(42), poison.clone()).force(), 42);
        assert!(!poison.is_evaluated());
    }
}

mod lazy_branch {
    include!(concat!(env!("H2R_CANARY_DIR"), "/lazyBranch.rs"));
    #[test]
    fn case_inside_unused_argument_does_not_force_scrutinee() {
        let poison = HInt::defer(|| panic!("deferred case entered early"));
        assert_eq!(h2r_entry(HInt::ready(13), poison.clone()).force(), 13);
        assert!(!poison.is_evaluated());
    }
}

mod lazy_unused {
    include!(concat!(env!("H2R_CANARY_DIR"), "/lazyUnused.rs"));
    #[test]
    fn unused_local_computation_remains_lazy() {
        let poison = HInt::defer(|| panic!("unused local computation forced"));
        assert_eq!(h2r_entry(HInt::ready(19), poison.clone()).force(), 19);
        assert!(!poison.is_evaluated());
    }
}

mod lazy_let {
    include!(concat!(env!("H2R_CANARY_DIR"), "/lazyLet.rs"));
    #[test]
    fn shared_local_captures_survive_and_are_not_forced_early() {
        let calls = std::rc::Rc::new(std::cell::Cell::new(0));
        let counter = calls.clone();
        let x = HInt::defer(move || {
            counter.set(counter.get() + 1);
            10
        });
        let result = h2r_entry(x, HInt::ready(11));
        assert_eq!(calls.get(), 0);
        assert_eq!(result.force(), 42);
        assert_eq!(result.force(), 42);
        assert_eq!(calls.get(), 1);
    }
}

mod lazy_nested {
    include!(concat!(env!("H2R_CANARY_DIR"), "/lazyNested.rs"));
    #[test]
    fn nested_thunks_retain_shared_outer_bindings() {
        let calls = std::rc::Rc::new(std::cell::Cell::new(0));
        let counter = calls.clone();
        let x = HInt::defer(move || {
            counter.set(counter.get() + 1);
            3
        });
        let result = h2r_entry(x, HInt::ready(4));
        assert_eq!(calls.get(), 0);
        assert_eq!(result.force(), 17);
        assert_eq!(calls.get(), 1);
    }
}

mod lazy_strict {
    include!(concat!(env!("H2R_CANARY_DIR"), "/lazyStrictUse.rs"));
    #[test]
    fn case_forces_the_shared_local_only_when_demanded() {
        let x = HInt::defer(|| 6);
        let result = h2r_entry(x.clone(), HInt::ready(9));
        assert!(!x.is_evaluated());
        assert_eq!(result.force(), 30);
        assert!(x.is_evaluated());
    }
}
