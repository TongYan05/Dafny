datatype classlist = NoneLeft | Cons(string, classlist)

// we don't care what this function does, other than it returns a number
function classHours  (s : string) : nat



function doTheWork(currClassHoursLeft : nat, classesAfterThat : classlist) : bool
decreases classesAfterThat,currClassHoursLeft
{
    if currClassHoursLeft == 0 then 
        match classesAfterThat 
        case NoneLeft => /* hooray! */ true
        case Cons(cname, rest) => doTheWork(classHours(cname), rest)
    else doTheWork(currClassHoursLeft - 1, classesAfterThat)
}

datatype list<T> = Nil | Cons (T, list<T>)
datatype tree = Node(element : int, children : list<tree>)

function sumTree(t : tree) : int
decreases t
{
    t.element + sumTreeList(t.children)
}

function sumTreeList(trees : list<tree>) : int
decreases trees
{
    match trees
    case Nil => 0
    case Cons(t, ts) => sumTree(t) + sumTreeList(ts)
}

// Function SumFrom(i,n) calculates 
//    i - (i+1) + (i + 2) - (i + 3) + (i + 4) ... +/- n
// with i and n integers; SumFrom(3,5) = 3 - 4 + 5 = 4
// Implementation strategy is to bounce back and forth between adding 
// positive integers (in SumFrom) and negative integers in SumFromNeg
function SumFrom(i: int, n: int): int
decreases n - i 
{
  if i >= n then n else i + SumFromNeg(i + 1, n)//>= is to prevent the function never stop, you can use > only, but it cannot satisfy the lemma
}
function SumFromNeg(i: int, n: int): int
decreases n - i 
{
  if i >= n then -n else -i + SumFrom(i + 1, n)
}

lemma sum35() ensures SumFrom(3,5) == 4 {}

lemma sumClosedForm(i:int, n:int) 
//   ensures SumFrom(i,n) == 

function ackermann(n : nat, m : nat) : nat
decreases m,n
{
    if m == 0 then n + 1 //n+
    else if n == 0 then ackermann(1, m - 1) // n+ m-
    else ackermann (ackermann(n - 1, m), m - 1)//n- m- as long as m is the dominant element, we do not care if ackermann(n - 1, m) is increasing or decreasing
}
/*
n m
3 5
25  4

