// include "../core-list.dfy"
datatype list<T> = Nil | Cons(head:T,tail:list<T>)
type lset = list<int>

function take<T>(n:nat, l:list<T>) : list<T>
{
    match l 
    case Nil => Nil 
    case Cons(h,t) => if n == 0 then Nil else Cons(h,take(n-1,t))
}
function drop<T>(n:nat, l:list<T>) : list<T>
{
    match l case Nil => Nil
    case Cons(h,t) => if n == 0 then l else drop(n-1,t)
}
function member(x : int, B : lset):bool
{
    match B
    case Nil => false
    case Cons(h,t) => if h == x then true else member(x,t)
}

function subset(A : lset, B : lset):bool
{
    match A
    case Nil => true
    case Cons(h,t) => if member(h,B) then subset(t,B) else false
}

function length<T>(l:list<T>):nat
{
    match l
    case Nil => 0
    case Cons(h,t) => 1 + length(t)
}

// chunks (2, [1,2,3,4]) == [[1,2], [3,4]]
// chunks (3, [1,2]) == [[1,2]]
// chunks (2, [1,2,3]) == [[1,2], [3]]
// chunks (0, [1,2,3]) == ??


lemma length_drop<T>(n:nat, l:list<T>)
    ensures length(drop(n,l)) == if n >= length(l) then 0 else length(l) - n
    {}
function chunks<T>(n : nat, l:list<T>) : list<list<T>>
  requires 0 < n 
  decreases length(l)
{
    match l 
    case Nil => Nil
    case Cons(head,tail) =>
        assert length(drop(n,l)) < length(l) by {length_drop(n,l);}
        Cons(take(n,l),chunks(n,drop(n,l)))
}
// type lset = list<int>

// predicate subset(A : lset, B : lset)
// {
//     match A
//     case Nil => true
//     case Cons(h,t) => member(h,B) && subset(t,B)
// }



lemma member_subset(x : int, A : lset, B : lset)
    requires member(x, A)
    requires subset(A, B)
    ensures member(x, B)
    decreases length(A)
    {}

lemma subset_trans(A : lset, B : lset, C : lset)
    requires subset(A,B)
    requires subset(B,C)
    ensures subset(A,C)
    {
        match A
        case Nil => 
        case Cons(h,t) =>
            assert member(h,B);
            assert subset(t,B);
            member_subset(h,B,C);
            subset_trans(t,B,C);
            assert member(h,C);
            assert subset(t,C);
    }
// chunks (3, [1,2]) == Cons(take(3, [1,2]), chunks(3, drop(3, [1,2]))
//                == Cons([1,2], chunks(3, []))
//                == Cons([1,2], [])
//                == [[1,2]]
