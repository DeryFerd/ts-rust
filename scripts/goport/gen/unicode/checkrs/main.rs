// Prints the generated Rust tables in the dump format of main.go (writeDump).
// gen.sh includes this file after `mod unicode_tables;`.

use unicode_tables::{RangeTable, map_get};

fn dump_table(t: &RangeTable) -> String {
    let mut b = String::from("r16");
    for &(lo, hi, stride) in t.r16 {
        b.push_str(&format!(" {lo}-{hi}/{stride}"));
    }
    b.push_str(" r32");
    for &(lo, hi, stride) in t.r32 {
        b.push_str(&format!(" {lo}-{hi}/{stride}"));
    }
    b.push_str(&format!(" lo={}", t.latin_offset));
    b
}

fn dump_map(name: &str, m: &[(&str, &'static RangeTable)]) {
    for &(k, t) in m {
        // map_get must find every key (the slice is sorted).
        let got = map_get(m, k).expect("map_get misses a key");
        assert!(
            std::ptr::eq(got, t),
            "map_get returns another table for {k}"
        );
        println!("{name} {k} {}", dump_table(t));
    }
    assert!(map_get(m, "Nope").is_none());
}

fn main() {
    println!("Version {}", unicode_tables::VERSION);
    dump_map("CATEGORIES", unicode_tables::CATEGORIES);
    for &(k, v) in unicode_tables::CATEGORY_ALIASES {
        assert_eq!(map_get(unicode_tables::CATEGORY_ALIASES, k), Some(v));
        println!("CATEGORY_ALIASES {k} {v}");
    }
    println!("CN {}", dump_table(&unicode_tables::CN));
    dump_map("SCRIPTS", unicode_tables::SCRIPTS);
    dump_map("FOLD_CATEGORY", unicode_tables::FOLD_CATEGORY);
    dump_map("FOLD_SCRIPT", unicode_tables::FOLD_SCRIPT);
    for &(lo, hi, [d0, d1, d2]) in unicode_tables::CASE_RANGES {
        println!("CASE_RANGES {lo}-{hi} {d0},{d1},{d2}");
    }
    for &(from, to) in unicode_tables::CASE_ORBIT {
        println!("CASE_ORBIT {from} {to}");
    }
    for (r, f) in unicode_tables::ASCII_FOLD.iter().enumerate() {
        println!("ASCII_FOLD {r} {f}");
    }
}
