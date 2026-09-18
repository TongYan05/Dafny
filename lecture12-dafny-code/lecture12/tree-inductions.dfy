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


function reverse<T>(l:list<T>) : list<T>
{
    match l case Nil => Nil
    case Cons(h,t) => append(reverse(t), Cons(h,Nil))
}

lemma length_append<T>(l1 : list<T>, l2:list<T>) 
  ensures length(append(l1,l2)) == length(l1) + length(l2) {}


datatype tree<V> = Lf | Node (k:int, v:V, tree<V>, tree<V>)

function size<V>(t : tree<V>) : nat
{
    match t case Lf => 0
    case Node(_, _, lt, rt) => size(lt) + size(rt) + 1
}

function mirror<V>(t:tree<V>) : tree<V>
{
    match t case Lf => Lf
    case Node(k,v,lt,rt) => Node(k,v,mirror(rt), mirror(lt))
}

function keys<V>(t:tree<V>) : list<int>
{
    match t case Lf => Nil
    case Node(k,_, lt, rt) => append(keys(lt), Cons(k, keys(rt)))
}

lemma {:induction false} test1<V>(t:tree<V>) 
  ensures size(mirror(t)) == size(t) 
  {
    match t case Lf => {}
    case Node(k,v,l,r) => {
        test1(l);
        test1(r);
        assert size(t) == size(l) + size(r) + 1;
        assert size(mirror(t)) == size(mirror(l)) + size(mirror(r)) + 1;
        assert size(l) == size(mirror(l));
    }
  }

lemma {:induction false} size_mirror<V>(t:tree<V>) 
  ensures size(mirror(t)) == size(t) 
  {
    match t case Lf => {
        assert size(t) == 0;
        assert size(mirror(t)) == 0;
    }
    case Node(k,v,l,r) => {
        size_mirror(l);// must smaller then t, otherwise the recursion is meaningless
        size_mirror(r);
    }
  }


lemma {:induction false} length_keys<V>(t:tree<V>)
  ensures length(keys(t)) == size(t) 
{
    match t case Lf => {
        assert size(t) == 0;
        assert length(keys(t)) == 0;
    }
    case Node(k,v,l,r) => {
        length_keys(l);
        length_keys(r);
        assert length(keys(l)) == size(l);
        assert length(keys(Node(k,v,Lf,r))) == size(Node(k,v,Lf,r));
        assert length(keys(Node(k,v,Lf,r))) + length(keys(l)) == size(l) + size(Node(k,v,Lf,r));
        assert size(t) == size(l) + size(Node(k,v,Lf,r));
        assert keys(t) == append(keys(l),keys(Node(k,v,Lf,r)));
        assert length(keys(t)) == length(keys(l)) + length(keys(Node(k,v,Lf,r))) by {
            length_append(keys(l),keys(Node(k,v,Lf,r)));
        }
    }
}