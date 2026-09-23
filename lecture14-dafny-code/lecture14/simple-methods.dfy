/* What *must* we assign to?  What *mustn't* we assign to? */
method maxMinMethod(i : int, j : int) returns (mx : int, mn:int)
  /* parens required around returns, even if there's only one */
{
    if i < j { mx := j; mn := i; }
    else { mx := i; mn := j ;}
    // i := 3; 不能给输入的变量赋值
}

method Main()
{
    // dafny is fussy here; can't put parens around x,n
    var x,n := maxMinMethod(10,3);
    print "Min is ", n, "; max is ", x, "\n";
}