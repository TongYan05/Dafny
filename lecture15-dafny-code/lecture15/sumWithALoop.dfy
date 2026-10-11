function sum(n:nat) : nat
{ 
    /* could equally use the recursive version */
    n * (n + 1) / 2  
}

method sumMd(n:nat) returns (s:nat)
  ensures s == sum(n)
{
    s := 0; 
    while s != sum(n)
      invariant s <= sum(n) 
      decreases sum(n) - s
}