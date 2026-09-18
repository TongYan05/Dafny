function swap_ish(x:int,y:int) : (int,int) {
    (y,x)
}

function swap(xy:(int,int)) : (int,int) {
    (xy.0,xy.1)
}

// implement f(x,y) = x^2 + x * y 
// in two different styles

method Main()
{
    print "A tuple: ", (3,true), "\n";
}

// 3D vectors would be fun