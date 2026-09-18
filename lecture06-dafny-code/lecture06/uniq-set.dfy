include "core-list.dfy"

predicate member(x : int, A : lset)
{
    match A 
    case Nil => false
    case Cons(y,ys) => x == y || member(x,ys)
}

predicate wfSet( A : lset)
{
    match A
    case Nil => true
    case Cons(x,xs) => !member(x,xs) && wfSet(xs)
}

/* functions to define
insert
delete
inter
union
card
subset
*/

/* lemmas to prove
member(x,insert(y,A)) <==> x == y || member(x,A)
member(x,delete(y,A)) <==> x != y && member(x,A)
member(x,union(A,B)) <==> member(x,A) || member(x,B)
member(x,inter(A,B)) <==> member(x,A) && member(x,B)
member(x,A) && subset(A,B) ==> member(x,B)

+ whatever well-formedness results we need and can manage
*/

function insert(x:int, A:lset) : lset
lemma member_insert(x:int, y:int, A:lset)
/* ? */ lemma wfSet_insert(x:int, A:lset) 


function delete(x:int, A : lset) : lset
lemma member_delete(x:int, y:int, A : lset) 
/* ? */ lemma wfSet_delete(x:int, A:lset) 


function inter(A:lset, B:lset) : lset
lemma member_inter(x:int, A : lset, B : lset)
/* ? */ lemma wfSet_inter(A:lset, B:lset)

predicate subset(A: lset, B : lset)
lemma member_subset(x:int, A : lset, B : lset)

function union(A:lset, B:lset): lset
lemma member_union(x:int, A:lset, B:lset)
/* ? */ lemma wfSet_union(A:lset, B:lset)
