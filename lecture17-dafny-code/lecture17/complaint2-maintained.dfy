/* COMPLAINT 2 :  "This loop invariant might not be maintained by
                   the loop."
 */


function ffn(n: nat) : nat
{ if n <= 1 then 1 else ffn(n-2) + ffn(n-1) }

// Example 1
method fibBroken(n0: nat) returns (f0: nat)
  ensures f0 == ffn(n0)
{
  var f1, n := 1, 0;
  f0 := 1;
  while (n < n0)
    invariant n <= n0
    invariant f0 == ffn(n)  
    invariant f1 == ffn(n + 1)
    invariant f0 <= f1
  {
    f0, f1, n    :=    f1, f0 + f1, n + 1;
  }
  assert n == n0;
}









/* --- Repair 1: add the missing conjunct -------------------------- */
/* After the assignment, f0 is the OLD f1 -- and we have said nothing
   at all about what f1 was.  So we cannot re-establish f0 == ffn(n). */
method fibFixed(n0: nat) returns (f0: nat)
  ensures f0 == ffn(n0)
{
  var f1, n := 1, 0;
  f0 := 1;
  while (n < n0)
    invariant n <= n0
    invariant f0 == ffn(n)
    invariant f1 == ffn(n+1)
/* Note WHICH line is flagged: not the one that is missing (it isn't
   there), but the one that can no longer be re-established without
   it.  */
  {
    f0, f1, n   :=   f1, f0 + f1, n + 1;
  }
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
    invariant r == x * m
  {
    x := x + 1;
    // r := r + x;//it is not x, it's the sum from 0 to n
    r := r + m;
  }
}









/* --- Repair 2: fix the body (the code really is wrong) ----------- */
/* r is supposed to be x copies of m.  The body adds x instead. */
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

/* The two look identical from the outside: same complaint, same line.
   Only reading the body tells you which repair you need. */
