use super::{Database, KeyType, ValueType};
use vstd::prelude::*;

verus! {

broadcast use vstd::seq_lib::group_seq_properties;

/// An immutable database whose entries may be in any order, with unique keys.
pub struct UnsortedVecDatabase {
    entries: Vec<(KeyType, ValueType)>,
}

impl View for UnsortedVecDatabase {
    type V = Map<KeyType, ValueType>;

    closed spec fn view(&self) -> Self::V {
        Map::new(
            self.entries@.map(|i: int, entry: (KeyType, ValueType)| entry.0).to_set(),
            |key: KeyType| self.entries@[choose|i: int|
                0 <= i < self.entries@.len() && #[trigger] self.entries@[i].0 == key].1,
        )
    }
}

impl UnsortedVecDatabase {
    #[verifier::type_invariant]
    closed spec fn well_formed(&self) -> bool {
        forall|i: int, j: int| #![trigger self.entries@[i], self.entries@[j]]
            0 <= i < j < self.entries@.len() ==> self.entries@[i].0 != self.entries@[j].0
    }

    /// Accept entries in arbitrary order. The caller must establish unique keys.
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
        proof { db.establish_view(); }
        db
    }

    proof fn establish_view(&self)
        requires self.well_formed(),
        ensures
            forall|i: int| #![trigger self.entries@[i]] 0 <= i < self.entries@.len()
                ==> self@.dom().contains(self.entries@[i].0)
                    && self@[self.entries@[i].0] == self.entries@[i].1,
            forall|key: KeyType| #![trigger self@.dom().contains(key)] self@.dom().contains(key)
                ==> exists|i: int| #![trigger self.entries@[i]]
                    0 <= i < self.entries@.len() && self.entries@[i] == (key, self@[key]),
    {
        assert forall|i: int| #![trigger self.entries@[i]] 0 <= i < self.entries@.len() implies
            self@.dom().contains(self.entries@[i].0)
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

    /// Insert one new key into a sorted output buffer used by `sort`.
    fn insert_ordered(input: &Vec<(KeyType, ValueType)>, entry: (KeyType, ValueType))
        -> (output: Vec<(KeyType, ValueType)>)
        requires
            forall|i: int, j: int| #![trigger input@[i], input@[j]]
                0 <= i < j < input@.len() ==> input@[i].0 < input@[j].0,
            forall|i: int| #![trigger input@[i]] 0 <= i < input@.len() ==> input@[i].0 != entry.0,
        ensures
            forall|i: int, j: int| #![trigger output@[i], output@[j]]
                0 <= i < j < output@.len() ==> output@[i].0 < output@[j].0,
            output@.contains(entry),
            forall|i: int| #![trigger input@[i]] 0 <= i < input@.len() ==> output@.contains(input@[i]),
            forall|i: int| #![trigger output@[i]] 0 <= i < output@.len()
                ==> output@[i] == entry || input@.contains(output@[i]),
    {
        let mut output = Vec::new();
        let mut i: usize = 0;
        while i < input.len() && input[i].0 < entry.0
            invariant
                i <= input.len(),
                output@.len() == i,
                forall|j: int| #![trigger output@[j]] 0 <= j < i ==> output@[j] == input@[j],
                forall|j: int| #![trigger input@[j]] 0 <= j < i ==> input@[j].0 < entry.0,
            decreases input.len() - i,
        {
            output.push(input[i]);
            i += 1;
        }
        let split = i;
        output.push(entry);
        while i < input.len()
            invariant
                split <= i <= input.len(),
                output@.len() == i + 1,
                output@[split as int] == entry,
                forall|j: int| #![trigger output@[j]] 0 <= j < split ==> output@[j] == input@[j],
                forall|j: int| #![trigger output@[j]] split < j <= i ==> output@[j] == input@[j - 1],
                forall|j: int| #![trigger input@[j]] 0 <= j < split ==> input@[j].0 < entry.0,
                forall|j: int| #![trigger input@[j]] split <= j < input@.len() ==> entry.0 < input@[j].0,
            decreases input.len() - i,
        {
            output.push(input[i]);
            i += 1;
        }
        proof {
            assert forall|j: int| #![trigger input@[j]] 0 <= j < input@.len()
                implies output@.contains(input@[j]) by {
                if j < split { assert(output@[j] == input@[j]); }
                else { assert(output@[j + 1] == input@[j]); }
            }
        }
        output
    }
}

impl Database for UnsortedVecDatabase {
    fn get(&self, key: &KeyType) -> (result: Option<&ValueType>) {
        proof { use_type_invariant(self); self.establish_view(); }
        let mut i: usize = 0;
        while i < self.entries.len()
            invariant
                i <= self.entries.len(),
                forall|j: int| #![trigger self.entries@[j]] 0 <= j < i ==> self.entries@[j].0 != *key,
            decreases self.entries.len() - i,
        {
            if self.entries[i].0 == *key {
                proof { use_type_invariant(self); self.establish_view(); }
                return Some(&self.entries[i].1);
            }
            i += 1;
        }
        None
    }

    fn scan(&self, lo: &KeyType, hi: &KeyType) -> (list: Vec<(KeyType, ValueType)>) {
        proof { use_type_invariant(self); self.establish_view(); }
        let mut list: Vec<(KeyType, ValueType)> = Vec::new();
        let mut i: usize = 0;
        while i < self.entries.len()
            invariant
                i <= self.entries.len(),
                self.well_formed(),
                forall|a: int, b: int| #![trigger list@[a], list@[b]]
                    0 <= a < b < list@.len() ==> list@[a].0 != list@[b].0,
                forall|a: int| #![trigger list@[a]] 0 <= a < list@.len()
                    ==> *lo <= list@[a].0 <= *hi,
                forall|a: int| #![trigger list@[a]] 0 <= a < list@.len()
                    ==> exists|j: int| #![trigger self.entries@[j]] 0 <= j < i && self.entries@[j] == list@[a],
                forall|j: int| #![trigger self.entries@[j]] 0 <= j < i && *lo <= self.entries@[j].0 <= *hi
                    ==> list@.contains(self.entries@[j]),
            decreases self.entries.len() - i,
        {
            let entry = self.entries[i];
            if *lo <= entry.0 && entry.0 <= *hi {
                proof {
                    assert forall|a: int| #![trigger list@[a]] 0 <= a < list@.len()
                        implies list@[a].0 != entry.0 by {
                        let j = choose|j: int| #![trigger self.entries@[j]] 0 <= j < i && self.entries@[j] == list@[a];
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
        proof { use_type_invariant(self); self.establish_view(); }
        let mut list: Vec<(KeyType, ValueType)> = Vec::new();
        let mut i: usize = 0;
        while i < self.entries.len()
            invariant
                i <= self.entries.len(),
                self.well_formed(),
                forall|a: int, b: int| #![trigger list@[a], list@[b]]
                    0 <= a < b < list@.len() ==> list@[a].0 < list@[b].0,
                forall|a: int| #![trigger list@[a]] 0 <= a < list@.len()
                    ==> exists|j: int| #![trigger self.entries@[j]] 0 <= j < i && self.entries@[j] == list@[a],
                forall|j: int| #![trigger self.entries@[j]] 0 <= j < i ==> list@.contains(self.entries@[j]),
            decreases self.entries.len() - i,
        {
            proof {
                assert forall|a: int| #![trigger list@[a]] 0 <= a < list@.len()
                    implies list@[a].0 != self.entries@[i as int].0 by {
                    let j = choose|j: int| #![trigger self.entries@[j]] 0 <= j < i && self.entries@[j] == list@[a];
                }
            }
            list = Self::insert_ordered(&list, self.entries[i]);
            i += 1;
        }
        proof {
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
