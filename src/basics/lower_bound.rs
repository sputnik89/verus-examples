use vstd::prelude::*;

verus! {

spec fn sorted(s: Seq<i64>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < s.len() ==> s[i] <= s[j]
}

fn lower_bound(vals: &Vec<i64>, key: i64) -> (index: usize)
    requires
        sorted(vals@),
    ensures
        (index as int) <= vals@.len(),
        forall|i: int| 0 <= i < (index as int) && (index as int) < vals@.len() ==> vals@[i] < key,
        forall|i: int| (index as int) <= i < vals@.len() ==> vals@[i] >= key,
{
    let mut i = 0;
    while i < vals.len() && vals[i] < key
        invariant
            i <= vals.len(),  // i == vals.len() at the last iteration
            forall|j: int| 0 <= j < (i as int) < vals@.len() ==> vals@[j] < key,  // i == vals.len() is out of bound
        decreases
            vals@.len() - i,
    {
        i += 1;
    }

    if i < vals.len() {
        assert(vals@[i as int] >= key);
        assert forall|j: int| (i as int) <= j < vals@.len() implies key <= vals@[j] by {
            assert(vals@[i as int] <= vals@[j]);
        }
    }

    i
}

fn main() {

}

}