// look at the brown!
lemma smallestExists()
  ensures exists s : nat :: forall m : nat :: s <= m 
{
  assert exists s : nat :: s == 0 && forall m : nat :: s <= m;
}
