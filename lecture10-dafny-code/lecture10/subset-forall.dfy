datatype list<T> = Nil | Cons(h:T,t:list<T>)
type lset = list<int>
function append<T>(l:list<T>,m:list<T>):list<T>
{
  match l
  case Nil => m
  case Cons(h,t) => Cons(h,append(t,m))
}


/* preliminaries: definitions of member, subset and reverse, 
   and a useful result about being a member of append (see 
   before when we were showing properties of union) */
predicate member(x:int, A:lset)
{
    match A 
    case Nil => false
    case Cons(y,ys) => x == y || member(x,ys)
}
predicate subset(A: lset, B : lset)
{
    match A 
    case Nil => true
    case Cons(x,xs) => member(x,B) && subset(xs,B)
}
lemma member_append(x:int, A:lset, B : lset)
  ensures member(x,append(A,B)) <==> member(x,A) || member(x,B)
{}
lemma member_subset(x:int,A : lset, B : lset)
  requires member(x,A)
  requires subset(A,B)
  ensures member(x,B)
  {}
lemma subset_forall(A : lset, B : lset)
  ensures subset(A,B) <==> forall x :: member(x,A) ==> member(x,B)
{
  if subset(A,B) {
    match A
    case Nil => {}
    case Cons(h,t) => {}
  }
  else {
    assert !subset(A,B);
    match A
    case Nil => {}
    case Cons(h,t) => {
      if !member(h,B) {
        assert member(h,A);
        assert exists x :: member(x,A) && !member(x,B);
      }
      else {
        assert !subset(t,B);
        assert exists x :: member(x,t) && !member(x,B);
      }
    }
  }
}




// this should now be easier
lemma subset_refl(A:lset) ensures subset(A,A) 
{
  match A
  case Nil => {}
  case Cons(h,t) => {
    assert member(h,A);
    assert forall x : int | member(x,t) :: member(x,A);
        assert subset(t,A) by {subset_forall(t,A);}
  }
}
function reverse<T>(l : list<T>) : list<T>
{
    match l
    case Nil => Nil
    case Cons(x,xs) => append(reverse(xs), Cons(x,Nil))
    // in nicer Haskell would be 
    // case l of 
    //   [] -> []
    //   x:xs -> reverse xs ++ [x]
}
lemma mem_reverse(x:int, A:lset)
  ensures member(x, reverse(A)) <==> member(x,A) 
{
  if member(x, reverse(A)) {
    assert member(x, reverse(A));
    match A 
    case Nil=> {}
    case Cons(h,t) => {
      assert reverse(A) == append(reverse(t),Cons(h,Nil));
      assert member(x,append(reverse(t),Cons(h,Nil)));
      assert member(x,A) by {member_append(x,reverse(t),Cons(h,Nil));}
    }
  }
  else {
    assert !member(x, reverse(A));
    match A 
    case Nil=> {}
    case Cons(h,t) => {
      assert reverse(A) == append(reverse(t),Cons(h,Nil));
      assert !member(x,append(reverse(t),Cons(h,Nil)));
      assert !member(x,A) by {member_append(x,reverse(t),Cons(h,Nil));}
    }
  }
  // match A 
  // case Nil=> {}
  // case Cons(y,ys) => {
  //   member_append(x,reverse(ys),Cons(y,Nil));
  // }
}

lemma reverse_subset(A:lset)
  ensures subset(reverse(A), A) 
  ensures subset(A, reverse(A))
{
  assert subset(reverse(A), A) by {
     subset_forall(reverse(A),A);
     forall x : int | member(x,reverse(A)) ensures member(x,A) {mem_reverse(x,A);}
  }
  assert subset(A,reverse(A)) by {
    subset_forall(A,reverse(A));
    forall x : int | member(x,A) ensures member(x,reverse(A)) {mem_reverse(x,A);}
  }

}


lemma prove1(l:lset)
  requires l != Nil
  ensures member(l.h,l)
  {}
lemma prove2(l:lset)
  requires l != Nil
  ensures subset(l.t,l)
  {
    match l
    case Cons(h,t) => {
      subset_forall(t, l);
      forall x : int | member(x,t) ensures member(x,l) {
        assert member(x,l);
      }
    }
  }








  // subset_forall(reverse(A), A);
  // subset_forall(A, reverse(A));

  // forall x | member(x, reverse(A)) {
  //   mem_reverse(x,A);
  // }
  // forall x | member(x, A) {
  //   mem_reverse(x,A);
  // }




 