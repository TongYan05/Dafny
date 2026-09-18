include "../core-list.dfy"

function take<T> (n:nat, l : list<T>) : list<T>
{
    if n == 0 then Nil
    else 
      match l 
      case Nil => Nil
      case Cons(h,t) => Cons(h, take(n-1, t))
}

// function drop<T>(n:nat, l : list<T>) : list<T> 

