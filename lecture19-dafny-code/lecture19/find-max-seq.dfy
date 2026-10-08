/* Lecture 19: the invariant is the postcondition, cut off at i.
   Ported from COMP1600 2025, tutorial 10 exercise 3. */

method find_max_incomplete(a: seq<int>) returns (m: int)
  requires |a| >= 1
  ensures forall j | 0 <= j < |a| :: a[j] <= m
  ensures exists j | 0 <= j < |a| :: a[j] == m
{
  var i := 1;
  m := a[0];
  while (i < |a|)
    // two ensures clauses, and each has a job to do in here as well.
    // what is true of the part of a we have looked at SO FAR?
    // (and how do we know, at the end, that "so far" is all of it?)
  {
    if a[i] >= m { m := a[i]; }
    i := i + 1;
  }
}












/* Each invariant is its postcondition with |a| replaced by i; the
   counting conjunct is what turns i >= |a| into i == |a| at the end. */
method find_max(a: seq<int>) returns (m: int)
  requires |a| >= 1
  ensures forall j :: 0 <= j < |a| ==> a[j] <= m
  ensures exists j :: 0 <= j < |a| && a[j] == m
{
  var i := 1;
  m := a[0];
  while (i < |a|)
    invariant i <= |a|
    invariant forall j :: 0 <= j < i ==> a[j] <= m
    invariant exists j :: 0 <= j < i && a[j] == m
  {
    if a[i] >= m { m := a[i]; }
    i := i + 1;
  }
}
