// A quadratic forumula with known solutions
//    (x - 2) * (x + 6) == x*x + 4 * x - 12
// which Dafny solves without any difficulty
lemma solve_quadratic(x:int)
  requires x * x + 4 * x - 12 == 0
  ensures x == 2 || x == -6//能自己解
{}


// Create a cubic where we know the solutions
//    (x - 3)(x - 2)(x + 6) 
// =  (x^2 - 5x + 6)(x + 6)
// =  (x^3 - 5x^2 + 6x + 6x^2 - 30x + 36)
// =  (x^3 + x^2 - 24x + 36)

// Note also that this is classic "Dafny will find this hard" 
// territory because of the heavy-duty multiplications, and 
// moving to cubics seems to push past whatever automation was 
// handling the quadratic so readily
lemma solve_poly(x : int)
  requires x * x * x + x * x - 24 * x + 36 == 0 
  ensures x == 3 || x == 2 || x == -6//自己解不出来
{
  assert x * x * x + x * x - 24 * x + 36 == (x - 3)*(x - 2)*(x + 6);
}

// remember fundamental fact about integer/nat-number division
lemma xltdiv(x:nat, y:nat, z:nat) 
  requires 0 < z
  ensures x < y / z <==> (x + 1) * z <= y //  (x + 1) * z < y + z <= y
{
  assert y == (y/z) * z + y % z ;
}