/* Lecture 19: quantified invariants over a seq, and nested loops.
   Ported from COMP1600 2025, tutorial 10 exercise 5. */

predicate dup_free(a: seq<int>)
{ forall i, j :: 0 <= i < j < |a| ==> a[i] != a[j] }

predicate sorted(a: seq<int>)
{ forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j] }

/* The easy case: sorted, so any duplicates are adjacent. */
method nodup_srt_incomplete(a: seq<int>) returns (b: bool)
  requires sorted(a)
  ensures b <==> dup_free(a)
{
  if |a| == 0 { return true; }
  var m: nat := |a| - 1;
  while m > 0
    // m counts down from the top of the sequence;
    // what do we know about the slice of the sequence
    // that we have looked at so far?
  {
    if a[m-1] == a[m] { return false; }
    m := m - 1;
  }
  return true;
}



/* The easy case: sorted, so any duplicates are adjacent. */
method nodup_srt(a: seq<int>) returns (b: bool)
  requires sorted(a)
  ensures b <==> dup_free(a)
{
  if |a| == 0 { return true; }
  var m: nat := |a| - 1;
  while m > 0
    invariant dup_free(a[m..])
  {
    if a[m-1] == a[m] { return false; }
    m := m - 1;
  }
  return true;
}



/* The general case, for the record.  Method works by checking
   each element in turn to see if it occurs in the rest of the 
   sequence (with a higher index). This version counts up.
*/
method nodup_incomplete(a: seq<int>) returns (b: bool)
  ensures b <==> dup_free(a)
{
  if |a| == 0 { return true; }
  var m : nat := 0;
  while m < |a| - 1 
    // stop one short of end to be able to compare with 
    // the very last element
  {
    var n : nat := m + 1;
    while n < |a|
    {
      if a[n] == a[m] { return false; }
      n := n + 1;
    }
    m := m + 1;
  }
  return true;
}

/* The general case, now with invariants.  

   Note that the inner loop's invariant carries the 
   OUTER loop's invariant as well: the inner loop
   is opaque just like a method call would be, so 
   Dafny has no idea what holds after the inner loop
   finishes unless we tell it.
*/
method nodup(a: seq<int>) returns (b: bool)
  ensures b <==> dup_free(a)
{
  if |a| == 0 { return true; }
  var m : nat := 0;
  while m < |a| - 1
    // stop one short of end to be able to compare with 
    // the very last element
    invariant m < |a|
    invariant forall i : nat | i < m :: a[i] !in a[i+1..]
  {
    var n : nat := m + 1;
    while n < |a|
      invariant m < n <= |a|
      invariant forall i : nat | i < m :: a[i] !in a[i+1..]
      invariant forall j : nat | m < j < n :: a[j] != a[m]
    {
      if a[n] == a[m] { return false; }
      n := n + 1;
    }
    m := m + 1;
  }
  return true;
}