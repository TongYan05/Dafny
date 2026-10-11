method moveUpTo(tgt : nat) returns (n:nat)
  ensures n == tgt
{
    n := 0;
    while n < tgt invariant n <= tgt {n := n + 1; }
}