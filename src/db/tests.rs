use super::{Database, SortedVecDatabase};

#[test]
fn empty_database() {
    let db = SortedVecDatabase::from_sorted(vec![]);
    assert_eq!(db.get(&0), None);
    assert!(db.scan(&i32::MIN, &i32::MAX).is_empty());
    assert!(db.sort().is_empty());
}

#[test]
fn lookup_and_inclusive_ranges() {
    let db = SortedVecDatabase::from_sorted(vec![(-5, 10), (0, 10), (3, -7), (9, 42)]);
    assert_eq!(db.get(&-5), Some(&10));
    assert_eq!(db.get(&3), Some(&-7));
    assert_eq!(db.get(&9), Some(&42));
    assert_eq!(db.get(&4), None);
    assert_eq!(db.get(&-6), None);
    assert_eq!(db.get(&10), None);
    assert_eq!(db.scan(&0, &9), vec![(0, 10), (3, -7), (9, 42)]);
    assert_eq!(db.scan(&3, &3), vec![(3, -7)]);
    assert!(db.scan(&4, &8).is_empty());
    assert!(db.scan(&10, &12).is_empty());
    assert!(db.scan(&-9, &-6).is_empty());
    assert_eq!(db.sort(), vec![(-5, 10), (0, 10), (3, -7), (9, 42)]);
}

#[test]
fn extreme_keys_and_singleton() {
    let db = SortedVecDatabase::from_sorted(vec![(i32::MIN, 1), (i32::MAX, 2)]);
    assert_eq!(db.get(&i32::MIN), Some(&1));
    assert_eq!(db.get(&i32::MAX), Some(&2));
    assert_eq!(db.scan(&i32::MIN, &i32::MAX), db.sort());
    assert_eq!(db.scan(&i32::MAX, &i32::MAX), vec![(i32::MAX, 2)]);
    let singleton = SortedVecDatabase::from_sorted(vec![(7, 8)]);
    assert_eq!(singleton.get(&7), Some(&8));
    assert_eq!(singleton.scan(&7, &7), vec![(7, 8)]);
    assert_eq!(singleton.sort(), vec![(7, 8)]);
}
