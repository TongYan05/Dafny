function f(x:int) :int { x + 1 }

/* Using + works, but what about subtraction */
function g(n:nat) :nat { n + f(n) }

/* absolute difference, but on nats */

method Main()
{
    print "g(10) = ", g(10), "\n";
}