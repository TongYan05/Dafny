/* Lecture 17: "the answer we want is the answer to what is left".
   Ported from COMP1600 2025, tutorial 9 exercise 5. */
/*





 A REALLY KEY POINT THAT WE HAVE TO CLAIM THE PRECONDITION OF A METHOD BEFORE WE CALL IT
                                 IN THE INVARIANT CLAUSE




*/
function euclid(n: nat, m: nat) : nat
  requires m <= n
{ if m == 0 then n else euclid(m, n % m) }

method gcd(n: nat, m: nat) returns (g: nat)
  requires m <= n
  ensures g == euclid(n, m)
{
  var f: nat;
  f, g := m, n;
  while (0 < f) 
  invariant f >= 0
  invariant f <= g
  invariant euclid( g , f ) == euclid(n, m)//when you call this method, you should claim f <= g, which is the precondition of the method!!!!!!
  {
    g, f   :=   f, g % f;
    
  }
}
