/* COMPLAINT 3 :  "A postcondition could not be proved on this return
                   path"

   Where to look: the squiggle lands on the method's opening left
   brace, NOT on the ensures clause.  (Dafny is complaining about the
   path through the body, not about the clause itself; the clause is
   named in the hover text.)  This is the least obvious of the three
   to find on screen.
 */



// Example 1
method countUpBroken(n: nat) returns (x: nat)
  ensures x == n
{
  x := 0;
  while (x < n)
    invariant x <= n
  { x := x + 1; }
}











/* --- Repair 1: add the counting conjunct ------------------------- */
/* `invariant true' passes questions 1 and 2 for free, and ALWAYS
   fails here.  At the end we know only x >= n. */
method countUpFixed(n: nat) returns (x: nat)
  ensures x == n
{
  x := 0;
  while (x < n)
    invariant x <= n            // x >= n and x <= n gives x == n
  { x := x + 1; }
}


// Example 2
method multBroken(m: int, n: int) returns (r: int)
  requires n >= 0
  ensures r == n * m
{
  var x := 0;
  r := 0;
  while (x < n)
    invariant x <= n
    invariant r == m * x
  {
    x := x + 1;
    r := r + m;
  }
}














/* --- Repair 2: strengthen the computing conjunct ----------------- */
/* The counting conjunct is there, so we do know x == n at the end.
   We know nothing whatever about r. */
method multFixed(m: int, n: int) returns (r: int)
  requires n >= 0
  ensures r == n * m
{
  var x := 0;
  r := 0;
  while (x < n)
    invariant x <= n
    invariant r == x * m
  {
    x := x + 1;
    r := r + m;
  }
}

// Example 3
// hint: how many times does the body run?
method toFiftyBroken() returns (i: int)
  // ensures i == 51
  ensures i == 50
{
  i := 0;
  while (i < 50)
    // invariant 0 <= i <= 51
    invariant 0 <= i <= 50

  { i := i + 1; }
}













/* --- Repair 3: the `ensures' is not what you meant --------------- */

/* Nothing is wrong with the loop.  It counts to 50, and 50 is not 51.
   No invariant can fix this one. */
method toFiftyFixed() returns (i: int)
  ensures i == 50
{
  i := 0;
  while (i < 50)
    invariant 0 <= i <= 50
  { i := i + 1; }
}

/* Complaint 3 does not know whether your loop is wrong or your
   specification is.  You have to decide which one you believe. */
