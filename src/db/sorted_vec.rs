use vstd::prelude::*;
use super::{Database, KeyType, ValueType};

verus! {

broadcast use vstd::seq_lib::group_seq_properties;

/// A database stored in strictly increasing key order.
pub struct SortedVecDatabase {
    entries: Vec<(KeyType, ValueType)>,
}

impl SortedVecDatabase {
    #[verifier::type_invariant]
    closed spec fn well_formed(&self) -> bool {
        forall|i: int, j: int| #![trigger self.entries@[i], self.entries@[j]] 0 <= i < j < self.entries@.len()
            ==> self.entries@[i].0 < self.entries@[j].0
    }

    /// Construct a database from entries with strictly increasing keys.
    pub fn from_sorted(entries: Vec<(KeyType, ValueType)>) -> (db: Self)
        requires
            forall|i: int, j: int| #![trigger entries@[i], entries@[j]] 0 <= i < j < entries@.len()
                ==> entries@[i].0 < entries@[j].0,
        ensures
            forall|k: KeyType| #![trigger db@.dom().contains(k)] db@.dom().contains(k)
                <==> exists|i: int| #![trigger entries@[i]] 0 <= i < entries@.len() && entries@[i].0 == k,
            forall|i: int| #![trigger entries@[i]] 0 <= i < entries@.len()
                ==> db@.dom().contains(entries@[i].0) && db@[entries@[i].0] == entries@[i].1,
    {
        let db = Self { entries };
        proof { db.entries_match_view(); }
        db
    }

    proof fn entries_match_view(&self)
        requires self.well_formed(),
        ensures
            forall|i: int| #![trigger self.entries@[i]] 0 <= i < self.entries@.len()
                ==> self@.dom().contains(self.entries@[i].0)
                    && self@[self.entries@[i].0] == self.entries@[i].1,
            forall|k: KeyType| #![trigger self@.dom().contains(k)] self@.dom().contains(k)
                ==> exists|i: int| #![trigger self.entries@[i]] 0 <= i < self.entries@.len() && self.entries@[i] == (k, self@[k]),
    {
        assert forall|i: int| #![trigger self.entries@[i]] 0 <= i < self.entries@.len() implies
            self@.dom().contains(self.entries@[i].0)
                && self@[self.entries@[i].0] == self.entries@[i].1 by {
            let k = self.entries@[i].0;
            let keys = self.entries@.map(|i: int, e: (KeyType, ValueType)| e.0);
            assert(keys[i] == k);
            assert(keys.contains(k));
            assert(exists|j: int| #![trigger self.entries@[j]] 0 <= j < self.entries@.len() && self.entries@[j].0 == k);
            let j = choose|j: int| #![trigger self.entries@[j]] 0 <= j < self.entries@.len() && self.entries@[j].0 == k;
            assert(i == j);
        }
    }
}

impl View for SortedVecDatabase {
    type V = Map<KeyType, ValueType>;

    closed spec fn view(&self) -> Self::V {
        Map::new(
            self.entries@.map(|i: int, e: (KeyType, ValueType)| e.0).to_set(),
            |k: KeyType| self.entries@[choose|i: int| #![trigger self.entries@[i]] 0 <= i < self.entries@.len() && self.entries@[i].0 == k].1,
        )
    }
}

impl Database for SortedVecDatabase {
    fn get(&self, key: &KeyType) -> (result: Option<&ValueType>) {
        proof { use_type_invariant(self); self.entries_match_view(); }
        let mut i = 0;
        while i < self.entries.len()
            invariant
                i <= self.entries.len(),
                forall|j: int| #![trigger self.entries@[j]] 0 <= j < i ==> self.entries@[j].0 != *key,
            decreases self.entries.len() - i,
        {
            if self.entries[i].0 == *key {
                proof { use_type_invariant(self); self.entries_match_view(); }
                return Some(&self.entries[i].1);
            }
            i += 1;
        }
        None
    }

    fn scan(&self, lo: &KeyType, hi: &KeyType) -> (list: Vec<(KeyType, ValueType)>) {
        proof {
            use_type_invariant(self);
            self.entries_match_view();
        }
        let mut list: Vec<(KeyType, ValueType)> = Vec::new();
        let mut i = 0;
        while i < self.entries.len()
            invariant
                i <= self.entries.len(),
                forall|a: int, b: int| #![trigger self.entries@[a], self.entries@[b]] 0 <= a < b < self.entries@.len()
                    ==> self.entries@[a].0 < self.entries@[b].0,
                forall|a: int, b: int| #![trigger list@[a], list@[b]] 0 <= a < b < list@.len()
                    ==> list@[a].0 < list@[b].0,
                forall|a: int| #![trigger list@[a]] 0 <= a < list@.len()
                    ==> *lo <= (list@[a]).0 <= *hi,
                forall|a: int| #![trigger list@[a]] 0 <= a < list@.len()
                    ==> exists|j: int| #![trigger self.entries@[j]] 0 <= j < i && self.entries@[j] == list@[a],
                forall|j: int| #![trigger self.entries@[j]] 0 <= j < i && *lo <= self.entries@[j].0 <= *hi
                    ==> list@.contains(self.entries@[j]),
            decreases self.entries.len() - i,
        {
            let entry = self.entries[i];
            if *lo <= entry.0 && entry.0 <= *hi {
                proof {
                    assert forall|a: int| #![trigger list@[a]] 0 <= a < list@.len() implies list@[a].0 < entry.0 by {
                        let j = choose|j: int| #![trigger self.entries@[j]] 0 <= j < i && self.entries@[j] == list@[a];
                    }
                }
                list.push(entry);
            }
            i += 1;
        }
        proof {
            assert forall|k: KeyType| #![trigger self@.dom().contains(k)] self@.dom().contains(k) && *lo <= k <= *hi
                implies list@.contains((k, self@[k])) by {
                let j = choose|j: int| #![trigger self.entries@[j]] 0 <= j < self.entries@.len() && self.entries@[j] == (k, self@[k]);
            }
        }
        list
    }

    fn sort(&self) -> (list: Vec<(KeyType, ValueType)>) {
        proof {
            use_type_invariant(self);
            self.entries_match_view();
        }
        let mut list = Vec::new();
        let mut i = 0;
        while i < self.entries.len()
            invariant
                i <= self.entries.len(),
                list@ == self.entries@.take(i as int),
            decreases self.entries.len() - i,
        {
            list.push(self.entries[i]);
            i += 1;
            assert(list@ == self.entries@.take(i as int));
        }
        assert(list@ == self.entries@);
        list
    }
}

}
