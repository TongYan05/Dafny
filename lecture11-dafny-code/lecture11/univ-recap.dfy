predicate q(x:int) {true}
predicate r(x:int) {true}

lemma somename_arbitrary()
  ensures forall x | 0 < x :: q(x)
{
  forall x | 0 < x ensures q(x){
  
  }
}

lemma somename_instantiate(y:nat)
  requires forall x | 0 < x :: q(x)
  ensures r(y / 103)
{
  if 0 < y {
    assert q(y);
    assert r(y / 103);
    }

}