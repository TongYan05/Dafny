/* Lecture 16: a *logical* accumulator.
   Ported from COMP1600 2025, week10-code.dfy (method m). */

method anyZeroBelow(f: nat -> nat, n: nat) returns (found: bool)
  ensures found <==> exists i :: 0 <= i < n && f(i) == 0
{
  var x: nat := 0;
  found := false;
  while (x < n)
  {
    if (f(x) == 0) { found := true; }
    x := x + 1;
  }
}
