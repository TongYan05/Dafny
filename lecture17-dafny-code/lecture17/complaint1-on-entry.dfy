/* COMPLAINT 1 :  "This loop invariant might not hold on entry."
*/

/* Example 1 */
method multBroken(m: int, n: int) returns (r: int)
  requires n >= 0
  ensures r == n * m
{
  var x := 0;
  r := m;
  while (x < n)
    invariant x <= n
    invariant r == x * m
  {
    x := x + 1;
    r := r + m;
  }
}








/* --- Repair 1: initialise the variables properly ----------------- */
// issue was incorrect initialisation
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

/* Example 2 */
method countUpBroken(n: nat) returns (x: nat)
  ensures x == n
{
  x := 0;
  while (x < n)
    invariant x == n
  { x := x + 1; }
}

















// --- Repair 2: weaken the invariant  (== becomes <=)
// "x is n" is what's needed at the END, not all the way through
method countUpFixed(n: nat) returns (x: nat)
  ensures x == n
{
  x := 0;
  while (x < n)
    invariant x <= n            // true at entry, and still enough at exit
  { x := x + 1; }
}


// Example 3
// hint: for which values of n is the invariant true when the loop
//       is first reached?
method upToBroken(n: int) returns (x: int)
  ensures x == n
{
  x := 0;
  while (x < n)
    invariant x <= n
  { x := x + 1; }
}















/* --- Repair 3: add a `requires' to the method -------------------- */

/* nothing is wrong with the invariant; the METHOD is wrong.
   `x <= n' is false at entry when n is negative, and no invariant
   will rescue a loop that cannot count up to a negative number. */
method upToFixed(n: int) returns (x: int)
  requires n >= 0               // <-- the repair
  ensures x == n
{
  x := 0;
  while (x < n)
    invariant x <= n
  { x := x + 1; }
}

/* equivalenty, could just declare the parameter `n: nat' 
   see countUpFixed above */
