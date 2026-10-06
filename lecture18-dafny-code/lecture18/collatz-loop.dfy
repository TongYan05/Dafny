/* Lecture 18: lecture 7's Collatz, now as a loop. */

method collatz(n0: nat) returns (n: nat)
  requires n0 > 0
  ensures n == 1           // "IF it finishes"
  decreases *
{
  n := n0;
  while (n > 1)
    invariant n > 0
    decreases *
  {
    if n % 2 == 0 { n := n / 2; } else { n := 3*n + 1; }
  }
}
