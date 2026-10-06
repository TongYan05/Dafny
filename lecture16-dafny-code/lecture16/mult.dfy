/* Lecture 16: counting + computing.
   Ported from COMP1600 2025, week10-code.dfy (mult). */

method mult(m: int, n: int) returns (r: int)
  requires n >= 0
  ensures r == n * m
{
  var x: int;
  r, x := 0, 0;
  while (x < n)
    invariant true     // counting
    invariant true  // computing
  {
    x := x + 1;
    r := r + m;
  }
}

/* Try deleting each invariant in turn, and read the complaint. */
