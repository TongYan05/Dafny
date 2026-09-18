lemma imp_conj_equiv(p:bool, q:bool, r:bool)
// ensures p ==> q ==> r ...

// de-morgan : (¬(A ∧ B) ⇔ ¬A ∨ ¬B) ∧ (¬(A ∨ B) ⇔ ¬A ∧ ¬B)

// and-distributes over or

// or-distributes over and

// implication is just fancy disjunction