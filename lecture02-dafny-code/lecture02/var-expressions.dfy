// "let" expressions in Dafny

function expanded(x:int) : int
{
    if x * 10 > 63 then x * 10 + 7 else x * 10 + 1
}

// if only we didn't have to keep writing x * 10 again and again and again and again

