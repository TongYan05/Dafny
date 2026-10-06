/* Lecture 18: we know it stops; we cannot say why.
   Ported from COMP1600 2025, week11-code.dfy (crystal_ball). */

function f(n:nat) : nat
{
  if n == 100 || n > 200 then 0 else 1
}

method crystal_ball() returns (z: nat)
  requires exists k : nat :: f(k) == 0
  ensures f(z) == 0
  ensures forall z0 : nat | z0 < z :: f(z0) != 0
{
  var k : nat :| f(k) == 0;
  z := 0;
  while (f(z) != 0) 
    invariant z <= k
    invariant forall z0 : nat | z0 < z :: f(z0) != 0
    decreases k - z
  { 
    z := z + 1; 
  }
}

method Main()
{
  assert f(500) == 0;
  var answer := crystal_ball();
  print "f is first zero on argument ", answer, "\n";
}
