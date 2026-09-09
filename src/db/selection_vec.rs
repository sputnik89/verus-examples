use super::{Database, KeyType, ValueType};
use vstd::prelude::*;

verus! {

broadcast use vstd::seq_lib::group_seq_properties;

/// Immutable entries with unique keys, stored in arbitrary order.
pub struct SelectionVecDatabase {
    entries: Vec<(KeyType, ValueType)>,
}

impl View for SelectionVecDatabase {
    type V = Map<KeyType, ValueType>;

    closed spec fn view(&self) -> Self::V {
        Map::new(
            self.entries@.map(|i: int, entry: (KeyType, ValueType)| entry.0).to_set(),
            |key: KeyType| self.entries@[choose|i: int|
                0 <= i < self.entries@.len() && #[trigger] self.entries@[i].0 == key].1,
        )
    }
}

impl SelectionVecDatabase {
    #[verifier::type_invariant]
    closed spec fn valid(&self) -> bool {
        forall|i: int, j: int| #![trigger self.entries@[i], self.entries@[j]]
            0 <= i < j < self.entries@.len() ==> self.entries@[i].0 != self.entries@[j].0
    }

    /// Construct from arbitrary-order entries whose keys are distinct.
    pub fn from_entries(entries: Vec<(KeyType, ValueType)>) -> (db: Self)
        requires
            forall|i: int, j: int| #![trigger entries@[i], entries@[j]]
                0 <= i < j < entries@.len() ==> entries@[i].0 != entries@[j].0,
        ensures
            forall|key: KeyType| #![trigger db@.dom().contains(key)]
                db@.dom().contains(key) <==> exists|i: int|
                    0 <= i < entries@.len() && #[trigger] entries@[i].0 == key,
            forall|i: int| #![trigger entries@[i]] 0 <= i < entries@.len()
                ==> db@.dom().contains(entries@[i].0) && db@[entries@[i].0] == entries@[i].1,
    {
        let db = Self { entries };
        proof { db.connect_view(); }
        db
    }

    proof fn connect_view(&self)
        requires self.valid(),
        ensures
            forall|i: int| #![trigger self.entries@[i]] 0 <= i < self.entries@.len()
                ==> self@.dom().contains(self.entries@[i].0)
                    && self@[self.entries@[i].0] == self.entries@[i].1,
            forall|key: KeyType| #![trigger self@.dom().contains(key)] self@.dom().contains(key)
                ==> exists|i: int| #![trigger self.entries@[i]]
                    0 <= i < self.entries@.len() && self.entries@[i] == (key, self@[key]),
    {
        assert forall|i: int| #![trigger self.entries@[i]] 0 <= i < self.entries@.len()
            implies self@.dom().contains(self.entries@[i].0)
                && self@[self.entries@[i].0] == self.entries@[i].1 by {
            let key = self.entries@[i].0;
            assert(self.entries@.map(|i: int, entry: (KeyType, ValueType)| entry.0)[i] == key);
            assert(exists|j: int| 0 <= j < self.entries@.len()
                && #[trigger] self.entries@[j].0 == key);
            let j = choose|j: int| 0 <= j < self.entries@.len()
                && #[trigger] self.entries@[j].0 == key;
            assert(i == j);
        }
    }

    /// Exchange two entries while preserving membership and distinct keys.
    fn exchange(list: &mut Vec<(KeyType, ValueType)>, a: usize, b: usize)
        requires
            a < old(list)@.len(), b < old(list)@.len(),
            forall|i: int, j: int| #![trigger old(list)@[i], old(list)@[j]]
                0 <= i < j < old(list)@.len() ==> old(list)@[i].0 != old(list)@[j].0,
        ensures
            final(list)@.len() == old(list)@.len(),
            forall|i: int| #![trigger final(list)@[i]] 0 <= i < final(list)@.len() ==>
                final(list)@[i] == old(list)@[if i == a { b as int } else if i == b { a as int } else { i }],
            forall|entry: (KeyType, ValueType)| #[trigger] final(list)@.contains(entry)
                <==> old(list)@.contains(entry),
            forall|i: int, j: int| #![trigger final(list)@[i], final(list)@[j]]
                0 <= i < j < final(list)@.len() ==> final(list)@[i].0 != final(list)@[j].0,
    {
        let ghost before = list@;
        let x = list[a];
        let y = list[b];
        list.set(a, y);
        list.set(b, x);
        proof {
            assert forall|entry: (KeyType, ValueType)| #[trigger] list@.contains(entry)
                <==> before.contains(entry) by {
                if before.contains(entry) {
                    let i = choose|i: int| 0 <= i < before.len() && before[i] == entry;
                    let j = if i == a { b as int } else if i == b { a as int } else { i };
                    assert(list@[j] == entry);
                }
                if list@.contains(entry) {
                    let i = choose|i: int| 0 <= i < list@.len() && list@[i] == entry;
                    let j = if i == a { b as int } else if i == b { a as int } else { i };
                    assert(before[j] == entry);
                }
            }
        }
    }
}

impl Database for SelectionVecDatabase {
    fn get(&self, key: &KeyType) -> (result: Option<&ValueType>) {
        proof { use_type_invariant(self); self.connect_view(); }
        let mut i: usize = 0;
        while i < self.entries.len()
            invariant
                i <= self.entries.len(),
                forall|j: int| #![trigger self.entries@[j]] 0 <= j < i ==> self.entries@[j].0 != *key,
            decreases self.entries.len() - i,
        {
            if self.entries[i].0 == *key {
                proof { use_type_invariant(self); self.connect_view(); }
                return Some(&self.entries[i].1);
            }
            i += 1;
        }
        None
    }

    fn scan(&self, lo: &KeyType, hi: &KeyType) -> (list: Vec<(KeyType, ValueType)>) {
        proof { use_type_invariant(self); self.connect_view(); }
        let mut list: Vec<(KeyType, ValueType)> = Vec::new();
        let mut i: usize = 0;
        while i < self.entries.len()
            invariant
                i <= self.entries.len(), self.valid(),
                forall|a: int, b: int| #![trigger list@[a], list@[b]]
                    0 <= a < b < list@.len() ==> list@[a].0 != list@[b].0,
                forall|a: int| #![trigger list@[a]] 0 <= a < list@.len() ==>
                    *lo <= list@[a].0 <= *hi
                    && exists|j: int| #![trigger self.entries@[j]] 0 <= j < i && self.entries@[j] == list@[a],
                forall|j: int| #![trigger self.entries@[j]] 0 <= j < i && *lo <= self.entries@[j].0 <= *hi
                    ==> list@.contains(self.entries@[j]),
            decreases self.entries.len() - i,
        {
            let entry = self.entries[i];
            if *lo <= entry.0 && entry.0 <= *hi {
                proof {
                    assert forall|a: int| #![trigger list@[a]] 0 <= a < list@.len()
                        implies list@[a].0 != entry.0 by {
                        let j = choose|j: int| #![trigger self.entries@[j]]
                            0 <= j < i && self.entries@[j] == list@[a];
                    }
                }
                list.push(entry);
            }
            i += 1;
        }
        proof {
            assert forall|key: KeyType| #![trigger self@.dom().contains(key)]
                self@.dom().contains(key) && *lo <= key <= *hi
                implies list@.contains((key, self@[key])) by {
                let j = choose|j: int| #![trigger self.entries@[j]]
                    0 <= j < self.entries@.len() && self.entries@[j] == (key, self@[key]);
            }
        }
        list
    }

    fn sort(&self) -> (list: Vec<(KeyType, ValueType)>) {
        proof { use_type_invariant(self); self.connect_view(); }
        let mut list: Vec<(KeyType, ValueType)> = Vec::new();
        let mut copied: usize = 0;
        while copied < self.entries.len()
            invariant
                copied <= self.entries.len(),
                list@ == self.entries@.take(copied as int),
            decreases self.entries.len() - copied,
        {
            list.push(self.entries[copied]);
            copied += 1;
            assert(list@ == self.entries@.take(copied as int));
        }
        assert(list@ == self.entries@);
        let mut i: usize = 0;
        while i < list.len()
            invariant
                i <= list.len(), list.len() == self.entries.len(),
                forall|entry: (KeyType, ValueType)| #[trigger] list@.contains(entry)
                    <==> self.entries@.contains(entry),
                forall|a: int, b: int| #![trigger list@[a], list@[b]]
                    0 <= a < b < list@.len() ==> list@[a].0 != list@[b].0,
                // The completed prefix precedes every subsequent entry.
                forall|a: int, b: int| #![trigger list@[a], list@[b]]
                    0 <= a < i && a < b < list@.len() ==> list@[a].0 < list@[b].0,
            decreases list.len() - i,
        {
            let mut smallest = i;
            let mut j = i + 1;
            while j < list.len()
                invariant
                    i < list.len(), i <= smallest < j <= list.len(),
                    forall|k: int| #![trigger list@[k]] i <= k < j ==> list@[smallest as int].0 <= list@[k].0,
                decreases list.len() - j,
            {
                if list[j].0 < list[smallest].0 {
                    smallest = j;
                }
                j += 1;
            }
            Self::exchange(&mut list, i, smallest);
            i += 1;
        }
        proof {
            assert forall|a: int| #![trigger list@[a]] 0 <= a < list@.len()
                implies self@.dom().contains(list@[a].0) && self@[list@[a].0] == list@[a].1 by {
                assert(list@.contains(list@[a]));
                assert(self.entries@.contains(list@[a]));
                let j = choose|j: int| 0 <= j < self.entries@.len() && self.entries@[j] == list@[a];
            }
            assert forall|key: KeyType| #![trigger self@.dom().contains(key)] self@.dom().contains(key)
                implies list@.contains((key, self@[key])) by {
                let j = choose|j: int| #![trigger self.entries@[j]]
                    0 <= j < self.entries@.len() && self.entries@[j] == (key, self@[key]);
            }
        }
        list
    }
}

}
