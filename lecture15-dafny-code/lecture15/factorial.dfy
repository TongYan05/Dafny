function factorial(n:nat) : nat
{
    if n < 1 then 1 else n * factorial(n-1)
}

method factMthd(n:nat) returns (f:nat)
  ensures f == factorial(n)
{
    var i := 0;
    f := 1;
    while i < n 
}