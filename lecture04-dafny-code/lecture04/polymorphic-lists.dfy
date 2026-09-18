datatype List1<T> = Single(T) | Cons1(hd:T, tl:List1<T>)

function singleton<T>(v : T) : List1<T>
{  // you would never call singleton when you could just write Single(v) anyway
    Single(v)
}

function SquareFirst(v : List1<int>) : int
{
    match v
    case Single(n) => n * n
    case Cons1(hd,_) => hd * hd
}

// what about a function to return the **last** element of a List1