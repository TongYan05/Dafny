/* Lecture 18: why Dafny insists.
   Ported from COMP1600 2025, week11-code.dfy (nt, ff). */

method nt()
  decreases *
  ensures false          // <-- and this VERIFIES
{
  var x, y := 0, 2;
  while (y == 2)
    decreases *
  { x := 0; }
  assert false;
}











// even more directly 
method ff()
  decreases *
  ensures false
{
  while true decreases * { }
}
