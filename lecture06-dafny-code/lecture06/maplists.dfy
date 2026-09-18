datatype option<V> = None|Some(V)
datatype list<V> = Nil|Cons(head:V,tail:list<V>)
// "dictionaries" are lists of integers (the keys), coupled 
// with the values, which can be anything (generic/polymorphic)
type intmap<V> = list<(int,V)>

ghost predicate member<T>(i :T, l : list<T>)
{
    match l
    case Nil=>false
    case Cons(head,tail)=> head==i || member(i,tail)
}
function keys<V>(m:intmap<V>) : list<int>
{
    match m
    case Nil=>Nil
    case Cons((k,v),tail)=> Cons(k,keys(tail))


    // match m case Nil => Nil
    // case Cons((k,_), kvs) => Cons(k,keys(kvs))
}

function insert<V>(m : intmap<V>, k:int, v:V) : intmap<V>
{
    Cons((k,v),m)


    // Cons((k,v), m)
}

function lookup<V>(m : intmap<V>, k:int) : option<V>
{
    match m
    case Nil=>None
    case Cons((h,v),tail)=> if k==h then Some(v) else lookup(tail,k)
}

lemma member_lookup<V>(m : intmap<V>, k : int, v : V)
  requires member((k,v), m)
  ensures exists u :: lookup(m,k) == Some(u)
{}

lemma lookup_some<V>(m : intmap<V>, k : int, v : V)
  ensures lookup(m,k) == Some(v) ==> member(k,keys(m))
  {}
