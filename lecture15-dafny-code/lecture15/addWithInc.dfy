// add with increments (+1s)
method addWI(m : nat, n:nat) returns (r:nat)
  ensures r == m + n
{
    var n0 := 0;
    r := m;
    while n0 < n  // try with != too
    invariant n0 <= n
    invariant r == m + n0
    invariant r <= m + n
    { 
        n0 := n0 + 1; //1 ...... n
        r := r + 1; // m ......... m + n
    }
}

method test()
{
    var i := 0;

    while i < 10
        // invariant true//that is always true
        invariant i <= 10
    {
        i := i + 1;
    }

    assert i == 10;// assert rely on the invariant and the negation of loop guard
}