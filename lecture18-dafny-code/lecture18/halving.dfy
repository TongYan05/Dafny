/* Lecture 18: the variant needs the invariant's help.
   Ported from COMP1600 2025, week11-code.dfy (m, m2). */

/* Halving one number while doubling the other is part of 
   the multiplication "trick" sometimes known as 
     “Russian Multiplication”
   Turn 16 * 12 == 8 * 24 == 4 * 48 == 2 * 96 == 1 * 192
*/
method halve_bad(m: int, n: int) returns (a: int, b: int)
  requires  m >= 0
  ensures a * b == m * n
{
  if m == 0 || n == 0 { return 0,0; }
  a, b := m, n;
  while (a % 2 == 0)
    invariant a * b == m * n
    invariant a >= 0
    decreases a
  { a := a / 2; b := b * 2; }
}









/* a non-cheating decreases measure, AND an invariant clause that 
   makes it all work */
method halve(m: nat, n: nat) returns (a: nat, b: nat)
  requires m > 0
  ensures a * b == m * n
{
  if m == 0 || n == 0 { return 0,0; }
  a, b := m, n;
  while (a % 2 == 0)
    decreases a
    invariant 0 < a
    invariant a * b == m * n
  { 
    // knowing 0 < a and a % 2 == 0 means a is 2, 4, 6, 8 ...
    a := a / 2; b := b * 2; 
    // so, after dividing by two it's still greater than 0,
    // though it may not be even anymore.  
    // (And that's the difference between an invariant and a guard!)
  }
}
