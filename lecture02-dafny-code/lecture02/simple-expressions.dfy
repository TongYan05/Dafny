function SquareAndAddOne(x:int) : int
{
    x * x + 1
}

function f(x : int, y:int) : int
{
    if x < y then y else x
}

function isEven(x:int) : bool{ x % 2 == 0 }
predicate isOdd (x:int) { x % 2 == 1}
predicate mystery(x:int) { !isEven(x) ==> true }

// write a function to compare size of x mod 4 and x + 1 mod 4.

method Main()
{
    print "f(6,5) = ", f(6,5), "\n";

    // and also
    print "SquareAndAddOne(-10) = ", SquareAndAddOne(-10), "\n";
    print "complicated = ", mystery(SquareAndAddOne(f(5,6))), "\n";
}