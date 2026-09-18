datatype lset = Nil | Cons(int,lset)

predicate member(i:int, A:lset) 
{
    match A 
    case Nil => false 
    case Cons(j,rest) => i == j || member(i,rest)
}

predicate all_distinct(A : lset) 
{
  match A
  case Nil => true
  case Cons(h,t) => !member(h,t) && all_distinct(t)
}

function nub(A : lset) : lset 
{
  match A 
  case Nil => Nil
  case Cons(x,xs) => if member(x,xs) then 
                      nub(xs)
                     else Cons(x,nub(xs))
} // the "nub" of an issue is its essence
