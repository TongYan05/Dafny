include "../core-list.dfy"

// OK
predicate member(i:int, s:lset) 
function insert(i:int, s:lset) : lset
function union (A : lset, B : lset) : lset 
function delete(i:int, A : lset) : lset
function intersect(A : lset, B : lset) : lset
predicate subset(A : lset, B : lset)

// work
lemma member_insert(x : int, y:int, A : lset) 
lemma member_delete(i:int, j:int, A:lset)
lemma member_inter(x:int, A:lset, B:lset)
lemma member_subset(x:int, A:lset, B:lset)

// feels like it should work
lemma member_union(x : int, A : lset, B : lset)

lemma subset_union(A : lset, B : lset, C : lset) 
lemma subset_refl(A : lset)
lemma subset_trans(A : lset, B : lset, C : lset)
