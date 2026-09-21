//! Executable checks of generated code with deferred, instrumented inputs.
#![allow(dead_code)]

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
