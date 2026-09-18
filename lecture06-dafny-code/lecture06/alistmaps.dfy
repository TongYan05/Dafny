// include "../core-list.dfy"
datatype option<V> = None|Some(V)
datatype list<V> = Nil|Cons(head:V,tail:list<V>)
// "dictionaries" are lists of integers (the keys), coupled 
// with the values, which can be anything (generic/polymorphic)
type dict<V> = list<(int,V)>

function lookup<V>(key:int, dict:dict<V>) : option<V>//“this function may return a value of type V, or it may return nothing.”
{
  match dict
  case Nil=>None
  case Cons((k,v),tail)=> if key==k then Some(v) else lookup(key,tail)//if the key do not exist, cannot return a v!! so use some(v)

    // match dict 
    // case Nil => None
    // case Cons((j,v), rest) => if j == key then Some(v) 
    //                         else lookup(key,rest)
}

function insert<V>(key : int, value : V, dict : dict<V>) : dict<V>
{
  match dict
  case Nil=>Cons((key,value),Nil)
  case Cons((k,v),tail)=> Cons((key,value),dict)


  // Cons((key,value), dict)
}

lemma lookup_insert<V>(d:dict<V>, k:int, v:V)
  ensures lookup(k,insert(k,v,d)) == Some(v) {}//lookup return option<V> so we use some(v)
