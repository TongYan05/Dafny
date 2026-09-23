datatype list<T> = Nil | Cons (hd:T, tl:list<T>)
function append<T>(l1:list<T>, l2:list<T>) : list<T>
{
    match l1 case Nil => l2
    case Cons(h,t) => Cons(h, append(t,l2))
}

datatype tree<V> = Lf | Node (k:int, v:V, tree<V>, tree<V>)

// v1: the natural version, but uses append.
// recursive calls builds keys(lt), and then that
// entire list is copied again on to the result
// of the Cons(k, keys(rt))
function keys<V>(t:tree<V>) : list<int>
{
    match t case Lf => Nil
    case Node(k,_,lt,rt) => append(keys(lt), Cons(k, keys(rt)))
}

// v2: accumulator-passing.  No appends at all, only Cons; 
//     will be O(n).
//     Read keysA(t, acc) as "the keys of t, followed by acc".
function keysA<V>(t:tree<V>, acc:list<int>) : list<int>
{
    match t case Lf => acc
    case Node(k,_,lt,rt) => keysA(lt, Cons(k, keysA(rt, acc)))
}

function keys2<V>(t:tree<V>) : list<int> { keysA(t, Nil) }

// what we actually want; not provable as it stands
lemma keys2_keys0<V>(t:tree<V>)
  ensures keys2(t) == keys(t) 

// the two facts about append we will use; 
// Dafny proves both automatically
lemma append_assoc<T>(a:list<T>, b:list<T>, c:list<T>)
  ensures append(a, append(b,c)) == append(append(a,b), c)
{}

lemma append_nil<T>(l:list<T>)
  ensures append(l, Nil) == l
{}

// the strengthened statement is just the sentence above, written down
lemma keysA_keys<V>(t:tree<V>, acc:list<int>)
  ensures keysA(t, acc) == append(keys(t), acc)
{
    match t
      case Lf => { }
      case Node(k, _, lt, rt) => {
        // (keys(lt) ++ (k : keys(rt))) ++ acc
        // keys(lt) ++ ((k : keys(rt))) ++ acc)
        append_assoc(keys(lt), Cons(k, keys(rt)), acc);
      }
}

// ... and the original falls out at acc == Nil
lemma keys2_keys<V>(t:tree<V>)
  ensures keys2(t) == keys(t)
{
  keysA_keys(t,Nil);
  append_nil(keys(t)); 
}
