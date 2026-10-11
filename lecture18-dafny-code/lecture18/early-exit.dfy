/* Lecture 18: a lexicographic measure, and an order on bool.
   Adapted from COMP1600 2025, week11-code.dfy (find, dec) --
   rewritten over a function rather than a seq, since sequences
   arrive next lecture. */

function f(n:nat) : nat

method findZero(n: nat) returns (found: bool)
  ensures found <==> exists i :: 0 <= i < n && f(i) == 0
{
  var i: nat := 0;
  found := false;
  while (i < n && !found)
    decreases n - i , !found
    invariant 0 <= i <= n
    invariant found <==> exists j :: 0 <= j < i && f(j) == 0// the correct version is adding break;
  {
    if f(i) == 0 { found := true; } else { i := i + 1; }
    // "early exit" via a found flag is a bit gross.
    // See below for alternative with break keyword.
  }
}

/* Dafny orders bool with false < true itself, but perhaps
   we don't want fellow humans to have to remember that; 
   can write functions like b2n to make things more explicit. */
/* false < true */
function b2n(b: bool) : nat { if b then 1 else 0 }



/* using the found flag in the guard makes for a nice 
   illustration of lexicographic ordering.
   Dafny can also let you write it the way you might
   prefer.   
*/
method findZero_with_break(n:nat) returns (found:bool)
  ensures found <==> exists i : nat | i < n :: f(i) == 0
{
  var c := 0;
  found := false;
  while c < n 
  decreases n - c
  invariant found <==> exists i : nat | i < c :: f(i) == 0
  {
    if f(c) == 0 { 
      found := true; 
      break; // return true; also works
    }
    c := c + 1;
  }
}