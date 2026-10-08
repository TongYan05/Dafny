/* Lecture 19 (challenge; 6260): a growing sequence, and a measure that
   is not its length.  Ported from COMP1600 2025, week11-code.dfy.

   swap11 replaces the first [1,1] in a sequence by [2,2,1];
   swap11s calls it until nothing changes. */

/* "number-ofs" : how many i's are there in sequence s */
function noofs(i: int, s: seq<int>) : nat
{
  if s == [] then 0
  else (if s[0] == i then 1 else 0) + noofs(i, s[1..])
}

/* given */
lemma noofs_plus(i: int, s: seq<nat>, t: seq<int>)
  ensures noofs(i, s + t) == noofs(i, s) + noofs(i, t)
{
  if (|s| == 0) { assert (s + t) == t; }
  else {
    assert (s + t) == [s[0]] + (s[1..] + t);
  }
}

/* given a sequence s with [1,1] present at position i,
   if we replace that chunk with [2,2,1], we have reduced
   the number of 1s. */
lemma ones_reduce(i: nat, s: seq<nat>)
  requires i <= |s| - 2
  requires s[i..i+2] == [1, 1]
  ensures noofs(1, s[..i] + [2, 2, 1] + s[i+2..]) < noofs(1, s)
  //      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  //        this is the important part
{
  noofs_plus(1, s[..i] + [2, 2, 1], s[i+2..]);
  noofs_plus(1, s[..i], [2, 2, 1]);
  assert s == (s[..i] + s[i..i+2]) + s[i+2..];
  noofs_plus(1, s[..i] + s[i..i+2], s[i+2..]);
  noofs_plus(1, s[..i], s[i..i+2]);
}


method swap11_incomplete(s1: seq<nat>) returns (s: seq<nat>, changed: bool)
  // the sequence gets larger, so |s| is no measure.  What does go down?
  // and the caller below needs to know it: a method is opaque, so
  // whatever progress this makes has to be said in an ensures clause.
  // ensures <SOMETHING_SENSIBLE>
{
  var i: nat := 0;
  s := s1;
  while i <= |s| - 2
  {
    if s[i..i+2] == [1, 1] {
      ones_reduce(i, s); // <--- HINT
      s := s[..i] + [2, 2, 1] + s[i+2..];
      return s, true;
    } else {
      i := i + 1;
    }
  }
  return s, false;
}

method swap11s_incomplete(s1: seq<nat>) returns (s: seq<nat>)
{
  var changed : bool := true;
  s := s1;
  while (changed)
    // and what did the call below just promise us?
  { s, changed := swap11_incomplete(s); }
}









/* The ensures clause is the only thing the outer loop can ever learn
   about a call -- including the fact that the call made progress. */
method swap11(s1: seq<nat>) returns (s: seq<nat>, changed: bool)
  ensures changed ==> noofs(1, s) < noofs(1, s1)
{
  var i: nat := 0;
  s := s1;
  changed := false;
  while i <= |s| - 2
    invariant s == s1 || noofs(1, s) < noofs(1, s1)
    decreases |s| - i
  {
    if s[i..i+2] == [1, 1] {
      ones_reduce(i, s);
      s := s[..i] + [2, 2, 1] + s[i+2..];
      return s, true;
    } else {
      i := i + 1;
    }
  }
}

method swap11s(s1: seq<nat>) returns (s: seq<nat>)
  // note absence of ensures clause here; it's quite hard to write 
  // the spec.  Can we say anything much at all?
{
  var changed : bool := true;
  s := s1;
  while changed
    decreases changed, noofs(1, s)
    // lexicographic combination not strictly required: could
    // come up with some sum as both measures always stay the same
    // or get smaller
  { s, changed := swap11(s); }
}
