function max(i : int, j : int) : int 
{
    if i < j then j else i
}

function min(i:int, j:int) : int
{ 
    if i < j then i else j
}

method maxMinMethod(i : int, j : int) returns (mx : int, mn:int)
  /* parens required around returns, even if there's only one */
  ensures mx == max(i,j)
  ensures mn == min(i,j)
  // and what else?
{
    // // if i < j { mx := j; mn := i; }
    // // else { mx := i; mn := j; }
    // if i < j {return j , i ;}
    // return i , j ;
    return max(i,j) , min(i,j);
}

method even(x : int) returns (result : bool){//write by myself
  result := false;
  if x % 2 == 0 {return !result;}
  return result;
}
// an example, dafny cannot use addOne implementation in another method, it can only use specifications
method addOne(x: int) returns (r: int)
//the solution is to add a specification here
ensures r == x + 1// this is what I added!
{
  r := x + 1;
}
method test()
{
  var y := addOne(5);
  assert y == 6;
}




method clamp(x: int, lo: int, hi: int) returns (r: int)
  requires lo <= hi// lo ....................... hi
  ensures lo <= r <= hi// lo.......r ..........hi
  ensures x < lo ==> r == lo
  ensures x > hi ==> r == hi
  ensures lo <= x <= hi <==> x == r
{
  if x < lo { return lo; }//lower bound
  if x > hi { return hi; }//upper bound
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
    ok,q,r := true, m/n, m%n;//you can just assign not return
}
