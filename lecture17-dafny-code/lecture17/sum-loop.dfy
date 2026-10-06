/* Lecture 17: the same loop, two invariants.
   Ported from COMP1600 2025, tutorial 10 exercise 2. */

function f(i : int) : int

// calculates f(l) + f(l + 1) + ... f(h-1)
function sum(l: int, h: int) : int
  decreases h - l
{ if h <= l then 0 else f(l) + sum(l+1, h) }

/* CANDIDATE B -- work still to do.  
   One trip round the loop is one unfolding of sum. */
method sum_loop(lo: int, hi: int) returns (s: int)
  ensures s == sum(lo, hi)
{
  var l, h := lo, hi;
  s := 0;
  while (l < h)
    invariant true
  {
    s := f(l) + s;
    l := l + 1;
  }
}

/* CANDIDATE A -- work already done.  True, but sum recurses at 
   the LEFT end, so Dafny needs an additional lemma to get round the 
   loop. */
method sum_loop2(lo: int, hi: int) returns (s: int)
  ensures s == sum(lo, hi)
{
  var l, h := lo, hi;
  s := 0;
  if lo >= hi { return s; }
  while (l < h)
    invariant s == sum(lo, l)
    invariant l <= h
  {
    s := f(l) + s;
    l := l + 1;
  }
}









lemma sum_add(lo: int, hi: int)
  requires lo <= hi
  ensures sum(lo, hi+1) == sum(lo, hi) + f(hi)
  decreases hi - lo
{
  if (lo < hi) { sum_add(lo+1, hi); }
}

