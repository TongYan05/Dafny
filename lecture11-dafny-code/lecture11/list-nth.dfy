datatype list<T> = Nil | Cons(T,list<T>)
function length<T>(l:list<T>):nat
{
  match l
  case Nil => 0
  case Cons(h,t) => 1 + length(t)
}

function member(i : int, l : list<int>) : bool
{
    match l 
    case Nil => false 
    case Cons(h,t) => h == i || member(i,t)
}

function nth<T>(l : list<T>, n : nat) : T
  requires n < length(l)
{
    match l 
    case Cons(h,t) => if n == 0 then h 
                      else nth(t, n - 1)
}

lemma mem_nth(i : int, l : list<int>)
  ensures member(i, l) <==> exists n : nat | n < length(l) :: nth(l,n) == i
  {
    match l// because nth has mathc clause
    case Nil =>
    case Cons(h,t) => {
      if member(i,l){ 
        if i == h {// the first situation of member(i,l)
          assert nth(l,0) == i; //initialization it
        }
        else { // the second situation of member(i,l)
          assert member(i,t); // have to state it this situation is member(u,t), otherwise dafny do not know
          var n : nat :| n < length(t) && nth(t,n) == i; // define an variable n, because there is no n in match clause
          assert nth(l,n+1) == i; //prove what we have to prove, just a variant
          assert n + 1 < length(l); // do not forget the precondition
          assert exists index : nat | index < length(l) :: nth(l,index) == i; // conclusion
        }
      }
      else {//prove from right to left, Dafny can prove itself

      }
    }
  }
