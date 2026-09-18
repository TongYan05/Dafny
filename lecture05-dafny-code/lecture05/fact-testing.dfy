function fact(n : nat) : nat
{
    if n < 2 then 1 else n * fact(n-1)
}

lemma fact3()
  ensures fact(3) == 6
{}

lemma fact6_big()
  ensures fact(6) > 10
{}

method Main()
{
    print "fact(20) == ", fact(20), "\n";
}

// testing on concrete values using proof is not 
// really what proof is good at...

// lemma fact20

// Symbolic results are better (factorials are never zero)
