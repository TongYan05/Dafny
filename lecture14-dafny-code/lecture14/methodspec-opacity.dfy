function max(i:int, j:int) : int
{ if i < j then j else i}

function exceed(i:int, j :int) : int
{ max(i,j) + 1}

lemma exceed_correct(i:int, j:int)
  ensures exceed(i,j) > i
  ensures exceed(i,j) > j 
{}

// In the Land of Methods things are not quite so rosy

method maxMethod(i:int, j:int) returns (mx:int)
{
    if i < j { mx := j; } else { mx := i; }
}

// this doesn't work
lemma maxMethod_lemma(i:int, j:int)
//  ensures maxMethod(i,j) == max(i,j)
{}

method exceedMethod(i:int, j:int) returns (exceeder:int)
  //ensures exceeder > i 
  //ensures exceeder > j
{
    var mx := maxMethod(i,j);
    exceeder := mx + 1;
}