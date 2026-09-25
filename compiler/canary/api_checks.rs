extern crate h2r_entry;

use std::rc::Rc;

use h2r_entry::{api_round_trip, on_program_stack};

fn measure() -> Rc<dyn Fn(String) -> Result<i64, String>> {
    Rc::new(|text: String| {
        if text.is_empty() {
            Err("empty".into())
        } else {
            Ok(i64::try_from(text.chars().count()).expect("a short string"))
        }
    })
}

#[test]
fn every_shape_crosses_into_haskell_and_back() {
    let result = on_program_stack(|| {
        api_round_trip(
            true,
            vec![1, 2, 3],
            Some("aλ".into()),
            ("xyz".into(), vec![(10, true), (20, false), (5, true)]),
            measure(),
        )
    });
    assert_eq!(
        result,
        (
            24,
            Some(vec!["aλ".into(), "λa".into(), "xyz".into()]),
            true,
            vec![Ok(2), Ok(3)]
        )
    );
}

#[test]
fn empty_values_cross_unchanged() {
    let result = on_program_stack(|| {
        api_round_trip(
            true,
            Vec::new(),
            None,
            (String::new(), Vec::new()),
            measure(),
        )
    });
    assert_eq!(result, (0, None, false, vec![Err("empty".into())]));
}
