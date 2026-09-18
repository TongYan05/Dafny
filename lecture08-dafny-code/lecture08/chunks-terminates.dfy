// include "../core-list.dfy"
datatype list<T> = Nil | Cons(T,list<T>)
function length<T>(l:list<T>):nat
{
    match l
    case Nil => 0
    case Cons(h,t) => 1 + length(t)
}
function take<T>(n:nat, l:list<T>) : list<T>
{ 
    match l 
    case Nil => Nil 
    case Cons(h,t) => if n == 0 then 
                        Nil 
                      else Cons(h,take(n-1, t))
}
function drop<T>(n:nat, l:list<T>) : list<T>
{
    match l case Nil => Nil
    case Cons(h,t) => if n == 0 then l else drop(n-1,t)
}

/* here's a pertinent lemma we proved earlier; 
   (could have used max as before instead of the if-then-else) 
   
   this proof is difficult
   
   */
lemma length_drop<T>(n:nat, l:list<T>)
   ensures length(drop(n,l)) == if n >= length(l) then 0 else length(l) - n {}

function chunks<T>(n:nat, l:list<T>) : list<list<T>>
  requires 0 < n
  decreases length(l)
{
    match l case Nil => Nil
    case _ => 
    assert length(drop(n,l)) < length(l) by {length_drop(n,l);}
    Cons(take(n,l),chunks(n,drop(n,l)))
}