use vstd::prelude::*;

verus! {

spec fn sorted(s: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] < s[j]
}

proof fn push_largest_preserves_sortedness(s: Seq<int>, x: int)
    requires
        sorted(s),
        forall|i: int| 0 <= i < s.len() ==> s[i] < x,
    ensures
        sorted(s.push(x)),
{
    assert forall|i: int, j: int| 0 <= i < j < s.push(x).len() implies s.push(x)[i] < s.push(x)[j]
    by
    {
        if j < s.len() {
            assert(s[i] < s[j]);
        } else {
            assert(j == s.len());
            assert(s.push(x)[j] == x);
            assert(i < s.len());
            assert(s[i] < x);
        }
    }   
}

fn main() {

}

}