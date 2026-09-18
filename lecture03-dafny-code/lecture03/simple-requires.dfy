datatype point = Point(x:int, y:int)

function gradient(p1:point, p2:point) : int
{ 
  // "rise over run"
  (p2.y - p1.y) / (p2.x - p1.x)
}