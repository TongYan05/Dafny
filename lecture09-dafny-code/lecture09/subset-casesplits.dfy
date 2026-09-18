datatype lset = Nil | Cons(int,lset)
predicate member(a : int, A : lset)
{
    match A case Nil => false
    case Cons(x,xs) => a == x || member(a,xs)
}

predicate subset(A : lset, B : lset) 
{
    match A 
    case Nil => true
    case Cons(x,xs) => member(x,B) && subset(xs,B)
}

lemma subset_member(x:int, A:lset, B:lset)
  requires member(x,A) requires subset(A,B)
  ensures member(x,B) {}

/* A ⊆ B ∧ B ⊆ C ⇒ A ⊆ C */
/* build  what-do-we-have   vs   what-do-want  table */
lemma subset_trans(A : lset, B : lset, C : lset)
  requires subset(A,B)
  requires subset(B,C)
  ensures subset(A,C) 
  {
    match A
    case Nil =>
    case Cons(head,tail) => {
      assert member(head,B);
      assert subset(tail,B);
      assert subset(B,C);
      assert member(head,C) by {subset_member(head,B,C);}
      assert subset(tail,C);
    }
  }


/* A ⊆ A */
function append(l:lset,m:lset):lset
{
  match l
  case Nil => m
  case Cons(h,t) => Cons(h,append(t,m))
}

lemma append_assoc(x:lset,y:lset,z:lset)
  ensures append(append(x,y),z) == append(x,append(y,z))
  {}

lemma subset_append(A:lset, B:lset)
  ensures subset(A, append(B, A))
{
  match A case Nil => {}
  case Cons(x,xs) =>
    assert member(x, append(B,A));
    assert subset(xs,append(append(B,Cons(x,Nil)),xs));
    assert append(append(B,Cons(x,Nil)),xs) == append(B,Cons(x,xs)) by {append_assoc(B,Cons(x,Nil),xs);}
    assert subset(xs,append(B,Cons(x,xs)));
}

lemma subset_refl(A : lset)
  ensures subset(A,A)
  {
    match A
    case Nil => 
    case Cons(h,t) =>{
      subset_append(t,Cons(h,Nil));
      assert append(Cons(h,Nil),t) == Cons(h,t);
    }
  }
  
