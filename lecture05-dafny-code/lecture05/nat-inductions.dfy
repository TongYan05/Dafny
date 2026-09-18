function sumUpTo(m:nat) : nat
{
    if m == 0 then 0 else m + sumUpTo(m - 1)
}

lemma sumUpTo_results()  
  // test on arguments 2, 3 and 100, a conjunctive claim

method Main()
{
    print "sum(2) ==", sumUpTo(2), "\n";
    print "sum(3) ==", sumUpTo(3), "\n";
    print "sum(100) == ", sumUpTo(100), "\n";
}

// what's the formula?
lemma triangle(m:nat)

