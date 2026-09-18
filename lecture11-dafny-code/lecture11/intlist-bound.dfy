datatype list<T> = Nil | Cons(head:T,tail:list<T>)
function length<T>(l:list<T>):nat
{
  match l
  case Nil => 0
  case Cons(h,t) => 1 + length(t)
}


predicate exceeds(i:int, l:list<int>) {
  match l 
  case Nil => true
  case Cons(h,t) => i > h && exceeds(i,t)
}


// will probably need an intermediate lemma
function max(a:int,b:int):int {if a > b then a else b}
function max_list(l:list<int>):int
requires l != Nil
{
  match l
  case Cons(h,Nil) => h
  case Cons(h,t) => max(h,max_list(t))
}
lemma max_list_exceeds(l:list<int>)
  requires l != Nil
  ensures exceeds(max_list(l) + 1, l)
{
  match l
  case Cons(h,Nil) => {}
  case Cons(h,t) => {
    assert max_list(l) + 1 > max_list(l);
    assert max_list(t) + 1 > max_list(t);
    assert exceeds(max_list(t) + 1, t);
    assert exceeds(max_list(Cons(h,Nil)) + 1, Cons(h,Nil));
    assert exceeds(max_list(Cons(h,t)) + 1, Cons(h,Nil));
    assert exceeds(max_list(Cons(h,t)) + 1, Cons(h,t));
  }
}

lemma boundExists(l : list<int>)
  ensures exists m :: exceeds(m,l)
{
  match l
  case Nil => {assert exceeds(1,l);}
  case Cons(h,t) => {
    assert exceeds(max_list(l) + 1, l) by {max_list_exceeds(l);}
  }
}
// flip quantifiers, prove something else
