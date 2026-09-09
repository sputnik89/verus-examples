use vstd::prelude::*;

verus! {

spec fn sorted_forall(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

spec fn sorted_recursive(s: Seq<i32>) -> bool
    decreases s,
{
    if s.len() <= 1 { true }
    else { s[0] <= s[1] && sorted_recursive(s.drop_first()) }
}

fn swap(s: &mut Vec<i32>, i: usize, j: usize)
    requires i < s@.len(), j < s@.len(),
    ensures final(s)@ == old(s)@.update(i as int, old(s)@[j as int])
                                .update(j as int, old(s)@[i as int]),
{
    let tmp = s[i];
    s[i] = s[j];
    s[j] = tmp;
}

fn sort(s: &mut Vec<i32>)
    ensures sorted_forall(final(s)@),
{
    let mut i = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            forall|k1: int, k2: int| 0 <= k1 < i && k1 < k2 < s@.len() ==> s@[k1] <= s@[k2],
        decreases s.len() - i,
    {
        let mut min_idx = i;
        let mut j = i;
        while j < s.len()
            invariant
                i <= j,
                i <= min_idx,  // needed for outer invariant
                min_idx < s.len(),
                forall|k: int| (i as int) <= k < (j as int) ==> s@[min_idx as int] <= s@[k],
            decreases s.len() - j,
        {
            if s[j] < s[min_idx] {
                min_idx = j;
            }
            j += 1;
        }
        assert(forall|k: int| i <= k < s@.len() ==> s@[min_idx as int] <= s@[k]);

        let ghost s_prev = s;
        swap(s, min_idx, i);

        // induction on loop invariant
        assert forall|k1: int, k2: int| 0 <= k1 < (i+1) && k1 < k2 < s@.len() implies s@[k1] <= s@[k2] by {
            if k1 == (i as int) {
                assert(s@[k1] == s@[i as int] == s_prev@[min_idx as int]);
                if k2 == min_idx {
                    assert(s_prev@[min_idx as int] == s@[i as int]);
                    assert(s_prev@[min_idx as int] <= s_prev@[i as int]);
                    assert(s@[k1] <= s@[k2]);
                } else {
                    assert(s_prev@[k2] == s@[k2]);
                    assert(s_prev@[min_idx as int] <= s_prev@[k2]);
                    assert(s@[k1] <= s@[k2]);
                }
            } else {
                assert(k1 < (i as int));
                if k2 == i {
                    assert(s_prev@[min_idx as int] == s@[k2]);
                    assert(k1 < (i as int) <= (min_idx as int));
                    assert(s@[k1] <= s@[min_idx as int]);
                    assert(s@[k1] == s_prev@[k1]);
                    assert(s@[k1] <= s@[k2]);
                } else if k2 == min_idx {
                    assert(s@[k2] == s_prev@[i as int]);
                    assert(s_prev@[k1] <= s_prev@[i as int]);  // induction hypothesis
                    assert(s_prev@[k1] == s@[k1]);
                    assert(s@[k1] <= s@[k2]);
                } else {
                    assert(s@[k1] <= s@[k2]);  // directly resulted from induction hypothesis
                }
            }
        }

        i += 1;
    }
}

}
