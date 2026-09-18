predicate foo(n:nat)

lemma dumb()
  requires forall n : nat :: 0 < n ==> foo(n)
  requires foo(0)
  ensures forall n : nat :: foo(n)
{
  assert forall n : nat :: foo(n);
}


