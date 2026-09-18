predicate fitsBetween(x : int, lo : int, hi : int)
  requires lo < hi
{
    lo < x < hi
}

lemma exist1(j:int)
  ensures exists i : int :: fitsBetween(i,2,14)
{
  assert fitsBetween(13,2,14);
}