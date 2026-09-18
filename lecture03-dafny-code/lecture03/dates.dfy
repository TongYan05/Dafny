datatype date = Date(day:nat, month:nat, year:nat)

function centuryNumber(d:date) : nat
{
    d.year / 100 + 1
}

// new syntax
const jan1_1900 : date := Date(1,1,1900)

method Main()
{
    print "1900 is in the ", centuryNumber(jan1_1900), "th century\n";
    // some people dispute this; they *are* pedants, but ...
}


