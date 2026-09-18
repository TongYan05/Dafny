include "../core-list.dfy"

function max(i : int, j : int) : int { if i < j then j else i}

function maxList(l : list<int>) : int
  requires l.Cons?
{
    match l 
    case Cons(j, Nil) => j
    case Cons(j, js) => max(j, maxList(js))
}

function maxA(l : list<int>, maxSoFar: int) : int
{
    match l case Nil => maxSoFar
    case Cons(j,js) => maxA(js, max(j, maxSoFar))
}

function maxList2(l : list<int>) : int
  requires l.Cons?
{
    match l case Cons(j,js) => maxA(js, j)
}

lemma maxA_thm(l:list<int>, A:int)
  // parameter order to lemma statement is important too
  // make the first parameter the one that is first in the 
  // definition of the recursive function and/or use the 
  // same decreases clause
  ensures maxA(l,A) == ???
{
}

lemma finishing_up(l : list<int>)
  requires l.Cons?
  ensures maxList(l) == maxList2(l)
{
}