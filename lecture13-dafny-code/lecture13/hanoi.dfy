// How many moves to shift n discs from pole 1 to pole 3?

function hanoi1(n : nat) : nat
{
    if n == 0 then 0
    else 1 + 2 * hanoi1(n-1)
}

// ... and the same thing with an accumulator

function hanoi2(n : nat, a : nat) : nat
{
    if n == 0 then a
    else hanoi2(n-1, 2 * a + 1)
}

// this is what we actually want, and Dafny won't do it:

lemma hanoi12(n : nat)
  ensures hanoi1(n) == hanoi2(n, 0)

// the accumulator moves in the recursive call, so pinning it at 0 leaves us
// with a useless inductive hypothesis.  Let it vary instead, and guess the
// relation from a few values (hanoi2(3,a) is 7, 15, 23, 31 for a = 0..3):

lemma hanoi_gen(n : nat, a : nat)
  ensures hanoi2(n, a) == hanoi1(n) + a * (hanoi1(n) + 1)
{}

// same statement, quantifier written out; also automatic

lemma hanoi_gen2(n : nat)
  ensures forall a : nat :: hanoi2(n, a) == hanoi1(n) + a * (hanoi1(n) + 1)
{}

// and now the original falls out at a == 0

lemma hanoi12_again(n : nat)
  ensures hanoi1(n) == hanoi2(n, 0)
{ hanoi_gen(n,0); }
