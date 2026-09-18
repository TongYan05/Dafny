function fact(n:nat) : nat {
    if n < 2 then 1 else n * fact(n-1)
}

lemma fact6() 
  ensures fact(6) == 720
  {}

// a "universal property" about fact and <