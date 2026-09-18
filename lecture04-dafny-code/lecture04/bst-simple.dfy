datatype bst = Lf
| Node(key: string, value: int, left : bst, right : bst)

/* 
A three element tree:

           "j", 6
          /       \
     "i", 7       "k", -2


*/
const t3 : bst := Node("j", 6, Node("i", 7, Lf, Lf), Node ("k", -2, Lf, Lf))

function build2(k1:string, k2:string, v1:int, v2:int) : bst
// complete!