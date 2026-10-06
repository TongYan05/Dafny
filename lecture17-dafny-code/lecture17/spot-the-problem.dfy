/* Lecture 17: which of the three questions fails?
   Snippets from COMP1600 2025, tutorial 9, exercises 1 and 6. */

/* --- pair one ------------------------------------------------- */

/* fine: the guard failing IS what we want */
method problem1()
{
  var x := 20;
  while (x < 20)
    invariant x % 2 == 0
  assert x == 20;
}


method broken3()
{
  var i := 0;
  while (i < 97)
    invariant 0 <= i <= 99
  // { i := i + 1; } 
  assert i == 99;          // complaint 3
}
