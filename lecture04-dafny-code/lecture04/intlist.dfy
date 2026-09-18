datatype intlist = Empty 
  | Cons(hd:int, tl:intlist)

// write some variations on this with selectors ".fldname" and 
// pattern-matching to get particular output numbers
function dumb() : int
  ensures dumb() == 0
{
    var l := Cons(0,Cons(1,Cons(2,Empty)));
    l.hd
}