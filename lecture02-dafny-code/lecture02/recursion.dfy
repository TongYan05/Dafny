// the world's favourite recursive function
function factorial(x:nat) : nat {
    if x < 2 then 1 else x * factorial(x - 1)
}

function exp(m:nat, p:nat) : nat {
    if p == 0 then 1
    else m * exp(m,p-1)
}

method Main()
{
    print "factorial(10) = ", factorial(10), "\n";
    print "exp(3,5) = ", exp(3,5), "\n";
}

// not all recursions will keep Dafny happy..

// lack of base case
function bad1(m:nat):nat

// recursion dodginess (1 - wrong direction)
function bad2(m:nat):nat

// recursion dodginess (2 - falling off the bottom)
function bad3(i:int) : int
