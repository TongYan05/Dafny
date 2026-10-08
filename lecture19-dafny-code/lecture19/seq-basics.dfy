/* Lecture 19: sequences, by demonstration. */

method basics()
{
  var s : seq<int> := [3, 1, 4, 1, 5];
  var n:nat :| n <= 5;

  assert |s| == 5;
  assert s[0] == 3;
  assert s[4] == 5;

  /* slices are half-open with right index omitted */
  /* pretend there's a parenthesis on the right end
     if you know/are-used-to interval notation like
     (1..3) vs [1..3] vs (1..3] */
  assert s[1..3] == [1, 4];
  assert s[..2] == [3, 1];
  // assert s[3..] == ??;
  assert s[..] == s;
  assert s[..2] + s[2..] == s;
  // assert |s[..2]| == ??
  // assert |s[..n]| == ??
  // assert [1,2,3][1] == ??;
  assert forall t : seq<int> :: t[..|t|] == t;

  /* lots of ways for these to go wrong; with
     Dafny checking indexing, just as it checks for
     division by zero */

  /* concatenation and membership */
  assert [1,2] + [3] == [1,2,3];
  assert 4 in s;
  assert 7 !in s;

  /* update makes a NEW sequence */
  var t := s;
  s := s[0 := 99];
  assert t[0] == 3;
  assert s[0] == 99;

  /* multisets forget order but not multiplicity */
  assert multiset([3,1,4,1,5]) == multiset([1,1,3,4,5]);
  assert multiset([1,1]) != multiset([1]);

  // multisets can be written with { }, and compared with
  // < and <=
  assert multiset{1,2} < multiset{1,1,2};
}

method lenPlusOne<T>(s : seq<T>) returns (n:nat)
  ensures n == |s| + 1
{
   return |s| + 1;
}

method msLen<T>(ms : multiset<T>) returns (n:nat)
  ensures n == |ms| + 1
