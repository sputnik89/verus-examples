use vstd::prelude::*;

verus! {

// returns the minimum element from the given vector
// incorrect spec + correct implementation + correct proof (? might be incorrect because of incorrect spec)
fn min(s: &Vec<i32>) -> (m: i32)
    requires s.len() > 0,
    ensures forall|i: int| 0 <= i < s@.len() ==> s@[i] <= m,  // wrong
{
    let mut i = 0;
    let mut min_idx = i;
    while i < s.len()
        invariant
            min_idx < s.len(),
            forall|k: int| 0 <= k < i ==> s@[k] >= s@[min_idx as int],
        decreases s.len()-i,
    {
        if s[i] < s[min_idx] {
            min_idx = i;
        }
        assert(min_idx < s.len());
        i += 1;
    }
    assert(min_idx < s.len());
    s[min_idx]
}
}