//! Rust runs each test on a thread with a 2 MiB stack.

mod bench_text {
    include!(concat!(env!("H2R_CANARY_DIR"), "/benchText.rs"));
    #[test]
    fn a_tail_case_over_a_million_cells_stays_in_the_dispatcher() {
        assert_eq!(h2r_entry(1_000_000, 3), 250_000);
    }
}

mod bench_cps {
    include!(concat!(env!("H2R_CANARY_DIR"), "/benchCps.rs"));
    #[test]
    fn a_million_tail_calls_through_a_closure_stay_in_the_dispatcher() {
        assert_eq!(h2r_entry(1_000_000, 3), 3);
    }
}

mod bench_loop {
    include!(concat!(env!("H2R_CANARY_DIR"), "/benchLoop.rs"));
    #[test]
    fn a_million_tail_calls_returning_a_boxed_int_chase_in_constant_stack() {
        assert_eq!(h2r_entry(1_000_000, HInt::ready(3)).force(), 1_000_003);
    }
}
