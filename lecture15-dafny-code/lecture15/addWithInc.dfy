// add with increments (+1s)
method addWI(m : nat, n:nat) returns (r:nat)
  ensures r == m + n
{
    var n0 := 0;
    r := m;
    while n0 < n  // try with != too
    { 
        n0 := n0 + 1; 
        r := r + 1; 
    }
}