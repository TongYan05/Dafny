/* Lecture 17: when no invariant will do, and the PRECONDITION is missing.
   Ported from COMP1600 2025, tutorial 10 exercise 4.

   Take it in turns to remove 1 or 2 coins.
   Strategy: mirror the opponent so that three go each round. */

method coingame(ncoins: int) returns (win: bool)
  requires ncoins > 1  
  requires ncoins % 3 == 1
  ensures win
{
  var n  := ncoins;
  while (n > 1)
  invariant n >= 1
  invariant (ncoins - n) % 3 == 0
  {
    var i :| 1 <= i <= 2; // <--  i  is opponent move
    n := n - i;
    n := n - (3 - i);     // <-- 3-i is my response
  }
  win := (n == 1);
}
