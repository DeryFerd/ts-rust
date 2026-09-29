//! Port of internal/compiler/checkerpool_test.go (#4313): the checker
//! association functions. They need no program, so the tests run in this
//! process.

use super::Subtests;
use ts_goport::program::ls_program::{
    CHECKER_ASSOCIATION_BALANCE_PENALTY_MULTIPLIER, CHECKER_ASSOCIATION_PRIORITIZED_SOURCE_PENALTY,
    CHECKER_ASSOCIATION_SOURCE_FILE_WEIGHT_MULTIPLIER, CheckerAssociationPolicy,
    get_checker_association_base_weight, get_checker_association_order,
    get_checker_association_policy, get_checker_association_weights,
    get_checker_associations_in_order, should_prioritize_source_files,
};

// Go: compiler/checkerpool_test.go:8 TestGetCheckerAssociationBaseWeight
#[test]
fn test_get_checker_association_base_weight() {
    let got = get_checker_association_base_weight(100, 2500);
    assert_eq!(
        got, 125,
        "getCheckerAssociationBaseWeight() = {got}, want 125"
    );
}

// Go: compiler/checkerpool_test.go:15 TestShouldPrioritizeSourceFiles
#[test]
fn test_should_prioritize_source_files() {
    assert!(
        should_prioritize_source_files(1000, 100, 4),
        "shouldPrioritizeSourceFiles() = false, want true"
    );
    assert!(
        should_prioritize_source_files(1000, 125, 4),
        "shouldPrioritizeSourceFiles() = false at boundary, want true"
    );
    assert!(
        !should_prioritize_source_files(1000, 126, 4),
        "shouldPrioritizeSourceFiles() = true, want false"
    );
}

// Go: compiler/checkerpool_test.go:28 TestGetCheckerAssociationPolicy
#[test]
fn test_get_checker_association_policy() {
    struct Test {
        name: &'static str,
        total_weight: i64,
        declaration_weight: i64,
        checker_count: usize,
        want: CheckerAssociationPolicy,
    }
    let tests = [
        Test {
            name: "source dominated at any checker count",
            total_weight: 1000,
            declaration_weight: 100,
            checker_count: 2,
            want: CheckerAssociationPolicy {
                prioritize_source_files: true,
                source_file_weight_multiplier: 1,
                balance_penalty_multiplier: CHECKER_ASSOCIATION_PRIORITIZED_SOURCE_PENALTY,
            },
        },
        Test {
            name: "declaration heavy with few checkers",
            total_weight: 1000,
            declaration_weight: 400,
            checker_count: 2,
            want: CheckerAssociationPolicy {
                prioritize_source_files: false,
                source_file_weight_multiplier: 1,
                balance_penalty_multiplier: 1,
            },
        },
        Test {
            name: "source dominated with many checkers",
            total_weight: 1000,
            declaration_weight: 50,
            checker_count: 8,
            want: CheckerAssociationPolicy {
                prioritize_source_files: true,
                source_file_weight_multiplier: 1,
                balance_penalty_multiplier: CHECKER_ASSOCIATION_PRIORITIZED_SOURCE_PENALTY,
            },
        },
        Test {
            name: "declaration heavy with many checkers",
            total_weight: 1000,
            declaration_weight: 400,
            checker_count: 4,
            want: CheckerAssociationPolicy {
                prioritize_source_files: false,
                source_file_weight_multiplier: CHECKER_ASSOCIATION_SOURCE_FILE_WEIGHT_MULTIPLIER,
                balance_penalty_multiplier: CHECKER_ASSOCIATION_BALANCE_PENALTY_MULTIPLIER,
            },
        },
    ];
    let mut t = Subtests::new("TestGetCheckerAssociationPolicy");
    for test in &tests {
        t.run(test.name, || {
            let got = get_checker_association_policy(
                test.total_weight,
                test.declaration_weight,
                test.checker_count,
            );
            if got != test.want {
                return Err(format!(
                    "getCheckerAssociationPolicy() = {got:?}, want {:?}",
                    test.want
                ));
            }
            Ok(())
        });
    }
    t.finish();
}

// Go: compiler/checkerpool_test.go:90 TestGetCheckerAssociationOrder
#[test]
fn test_get_checker_association_order() {
    let got = get_checker_association_order(&[5, 10, 7, 2], &[true, false, false, true], true);
    assert_eq!(
        got.as_deref(),
        Some(&[1, 2, 0, 3][..]),
        "getCheckerAssociationOrder() = {got:?}, want [1 2 0 3]"
    );
    let got = get_checker_association_order(&[5], &[false], false);
    assert!(
        got.is_none(),
        "getCheckerAssociationOrder() = {got:?}, want nil"
    );
}

// Go: compiler/checkerpool_test.go:100 TestGetCheckerAssociationWeights
#[test]
fn test_get_checker_association_weights() {
    struct Test {
        name: &'static str,
        base_weights: [i64; 3],
        import_counts: [i64; 3],
        want: [i64; 3],
    }
    let tests = [
        Test {
            name: "normalizes import work to syntax work",
            base_weights: [100, 50, 25],
            import_counts: [0, 1, 3],
            want: [100, 93, 154],
        },
        Test {
            name: "no imports preserves base weights",
            base_weights: [100, 50, 25],
            import_counts: [0, 0, 0],
            want: [100, 50, 25],
        },
    ];

    let mut t = Subtests::new("TestGetCheckerAssociationWeights");
    for test in &tests {
        t.run(test.name, || {
            let got = get_checker_association_weights(&test.base_weights, &test.import_counts);
            if got != test.want {
                return Err(format!(
                    "getCheckerAssociationWeights({:?}, {:?}) = {got:?}, want {:?}",
                    test.base_weights, test.import_counts, test.want
                ));
            }
            Ok(())
        });
    }
    t.finish();
}

// Go: compiler/checkerpool_test.go:134 TestGetCheckerAssociations
#[test]
fn test_get_checker_associations() {
    let mut t = Subtests::new("TestGetCheckerAssociations");

    t.run("empty", || {
        let got = get_checker_associations_in_order(
            &[],
            &[],
            None,
            4,
            CHECKER_ASSOCIATION_BALANCE_PENALTY_MULTIPLIER,
        );
        if !got.is_empty() {
            return Err(format!(
                "getCheckerAssociationsInOrder() = {got:?}, want nil"
            ));
        }
        Ok(())
    });

    t.run("balances disconnected files", || {
        let got = get_checker_associations_in_order(
            &[1, 1, 1, 1, 1, 1],
            &vec![Vec::new(); 6],
            None,
            3,
            1,
        );
        let want = [0, 1, 2, 0, 1, 2];
        if got != want {
            return Err(format!(
                "getCheckerAssociationsInOrder() = {got:?}, want {want:?}"
            ));
        }
        Ok(())
    });

    t.run("uses program order", || {
        let got = get_checker_associations_in_order(&[1, 3, 2], &vec![Vec::new(); 3], None, 2, 1);
        let want = [0, 1, 0];
        if got != want {
            return Err(format!(
                "getCheckerAssociationsInOrder() = {got:?}, want {want:?}"
            ));
        }
        Ok(())
    });

    t.run("keeps dense components together", || {
        let got = get_checker_associations_in_order(
            &[1, 1, 1, 1, 1, 1],
            &[
                vec![1, 2],
                vec![0, 2],
                vec![0, 1],
                vec![4, 5],
                vec![3, 5],
                vec![3, 4],
            ],
            None,
            2,
            1,
        );
        let want = [0, 0, 0, 1, 1, 1];
        if got != want {
            return Err(format!(
                "getCheckerAssociationsInOrder() = {got:?}, want {want:?}"
            ));
        }
        Ok(())
    });

    t.run("respects weighted balance cap", || {
        let weights = [8, 7, 6, 5, 4, 3, 2, 1];
        let got = get_checker_associations_in_order(
            &weights,
            &vec![Vec::new(); weights.len()],
            None,
            3,
            1,
        );
        let mut loads = [0; 3];
        for (i, &checker_index) in got.iter().enumerate() {
            loads[checker_index] += weights[i];
        }
        for (checker_index, &load) in loads.iter().enumerate() {
            if load > 13 {
                return Err(format!(
                    "checker {checker_index} load = {load}, want at most 13; associations = {got:?}"
                ));
            }
        }
        Ok(())
    });

    t.finish();
}
