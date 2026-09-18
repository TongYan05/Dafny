datatype intlist = Empty | Cons(hd: int, tl : intlist)

function singleton(i:int) : intlist
  // what ensures line might we write here?
{
  Cons(i, Empty)
}

// what more interesting functions might we write to build lists?
// - of different lengths
// - with successive elements
// - ?