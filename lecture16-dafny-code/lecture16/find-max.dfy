/* Lecture 16: the abstract heuristic -- a property, not a value.
   Ported from COMP1600 2025, week10-code.dfy (find_max). */

method find_max(f: int -> int, lo: int, hi: int) returns (max: int)
  requires lo <= hi
  ensures forall j :: lo <= j <= hi ==> f(j) <= f(max)
  // note: no attempt to say that max is least such value, 
  // though this is what implementation will do
{
  max := lo;
  var i := lo;
  while (i < hi)
  invariant i <= hi
  invariant max <= i
  invariant forall j :: lo <= j <= i ==> f(j) <= f(max)
  {
    i := i + 1;
    if f(i) > f(max) { max := i; }
  }
}
