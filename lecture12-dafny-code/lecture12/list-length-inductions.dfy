datatype list<T> = Nil | Cons (hd:T, tl:list<T>)
function length<T>(l:list<T>) : nat
{
    match l case Nil => 0
    case Cons(_,t) => 1 + length(t)
}
function append<T>(l1:list<T>, l2:list<T>) : list<T>
{
    match l1 case Nil => l2
    case Cons(h,t) => Cons(h, append(t,l2))
}

lemma {:induction false} length_append<T>(l1:list<T>, l2:list<T>)
  ensures length(append(l1,l2)) == length(l1) + length(l2)
{
  match l1
  case Nil => {}
  case Cons(h,t) => {
    length_append(t,l2);
  }
}

function reverse<T>(l:list<T>) : list<T>
{
    match l case Nil => Nil
    case Cons(h,t) => append(reverse(t), Cons(h, Nil))
}

lemma {:induction false} test<T>(l:list<T>)
  ensures length(reverse(l)) == length(l)
  {
    match l
    case Nil => {}
    case Cons(h,t) => {
      test(t);
      assert length(Cons(h,Nil)) + length(t) == length(l);
      assert reverse(l) == append(reverse(t),Cons(h,Nil));
      assert length(reverse(t)) == length(t);
      assert length(reverse(Cons(h,Nil))) == length(Cons(h,Nil));
      assert length(reverse(t)) + length(reverse(Cons(h,Nil))) == length(l);
      assert length(reverse(t)) + length(reverse(Cons(h,Nil))) == length(append(reverse(t),Cons(h,Nil))) by {
        length_append(reverse(t),reverse(Cons(h,Nil)));
      }
    }
  }

lemma {:induction false} length_reverse<T>(l:list<T>)
  ensures length(reverse(l)) == length(l)
{
  match l case Nil => {assert length(reverse(l)) == length(l);}
  case Cons(h,t) => {
    length_reverse(t);
    // assert length(append(reverse(t),Cons(h,Nil))) == length(reverse(t)) + length(Cons(h,Nil)) by {
      length_append(reverse(t),Cons(h,Nil));
    // }
    
  }
}