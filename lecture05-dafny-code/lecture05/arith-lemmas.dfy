lemma example1(i : int)
  // if integer i lies between 0 and 3, then i ≠ 3 − i
  // informal argument?

// same again, with/without requires

// making it stronger?

lemma ltmod(m:nat, n:nat)  // upper bound for mods






// ** Part 2 ** come back to

lemma posmul(x : int, y :int) ensures 0 < x * y <==> 

// xltdiv(x:nat, y:nat, z:nat) 0 < z ⇒ (x < y / z ⇔ (x + 1) * z ≤ y)

lemma xltdiv (x:nat, y:nat, z:nat)
