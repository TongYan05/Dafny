/* Lecture 17: two changing variables, two computing invariants.
   Ported from COMP1600 2025, tutorial 9 exercise 4. */

function ffn(n: nat) : nat
{ if n <= 1 then 1 else ffn(n-2) + ffn(n-1) }

method fibMthd(n0: nat) returns (f0: nat)
  ensures f0 == ffn(n0)
{
  var f1, n: nat;
  f0, f1, n := 1, 1, 0;
  while (n < n0)
    invariant n <= n0
    invariant f0 == ffn(n)
    invariant f1 == ffn(n+1)     // comment this out and read the complaint
  {
    f0, f1, n := f1, f0 + f1, n + 1;
  }
}
