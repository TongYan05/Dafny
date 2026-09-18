predicate divides(m:nat, n:nat) 
{
    if m == 0 then n == 0
    else n % m == 0
}

// checks if t and all numbers below it *don't* divide into n.
// when/if t gets as far as 1, then return true, as we've checked 
// everything down to that point
predicate primeCheck(t : nat, n : nat )
  requires 1 < n
{
    t <= 1 || (!divides(t,n) && primeCheck(t - 1, n))
}

// (4,35) should return true, even though 35 is not prime
// because it only checks to see if 4, 3 or 2 divide into
// 35, and none of them do.
lemma primeCheck_4_35()
  ensures primeCheck(4,35) {}

// the important property; need to prove and iff where the RHS
// is a forall
lemma primeCheck_forall(t: nat, n:nat)
  requires 1 < n
  ensures 
    primeCheck(t,n) <==> forall x : nat | 1 < x <= t :: !divides(x,n)
    // forall u | 1 < u <= t :: !divides(u,n) 
{
  // assert forall u:nat :: 1 < u <= t ==> !divides(u,n);
}

// subset(A,B) <==> forall x | member(x,A) :: member(x,B)
//             <==> forall x :: member(x,A) ==> member(x,B)