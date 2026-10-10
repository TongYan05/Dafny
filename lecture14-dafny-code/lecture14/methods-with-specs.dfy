method maxMinMethod(i : int, j : int) returns (mx : int, mn:int)
  /* parens required around returns, even if there's only one */
  ensures mx == max(i,j)
  ensures mn == min(i,j)
  // and what else?
{
    // if i < j { mx := j; mn := i; }
    // else { mx := i; mn := j; }
    if i < j {return j , i ;}
    return i , j ;
}

function max(i : int, j : int) : int 
{
    if i < j then j else i
}

function min(i:int, j:int) : int
{ 
    if i < j then i else j
}

method clamp(x: int, lo: int, hi: int) returns (r: int)
  requires lo <= hi
  ensures lo <= r <= hi
  ensures x < lo ==> r == lo
  ensures x > hi ==> r == hi
{
  if x < lo { return lo; }
  if x > hi { return hi; }
  return x;  // could be r := x;
}

method divmod(m:nat, n:nat) returns (ok:bool,q:nat,r:nat)
  ensures n == 0 ==> ok == false && q == 0 && r == 0
  ensures n != 0 ==> ok == true && q == m/n && r == m%n
{
    // could also write return false,0,0;
    if n == 0 { 
        ok,q,r := false,0,0; 
        return; 
    }
    ok,q,r := true, m/n, m%n;
}
