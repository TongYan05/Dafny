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
  ensures mx == max(i,j)
{
    // if i < j { mx := j; } else { mx := i; }
    if i < j {return j;}
    return i;
}

// this doesn't work
lemma maxMethod_lemma(i:int, j:int)
//  ensures maxMethod(i,j) == max(i,j) ensures里面不能有方法
{}

method exceedMethod(i:int, j:int) returns (exceeder:int)
  // ensures exceeder > i 
  // ensures exceeder > j
  ensures exceeder == max(i,j) + 1 
{
    var mx := maxMethod(i,j);
    exceeder := mx + 1;
}