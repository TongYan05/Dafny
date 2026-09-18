datatype option<V> = None | Some(V)
datatype tree<V> = Lf
  | Node(k : string, v : V, left : tree<V>, right : tree<V>)

function lookup<V>(t : tree<V>, key : string) : option<V> 

function insert<V>(t : tree<V>, key : string, value : V) : tree<V> 

function sz<T>(t:tree<T>) : nat 

// lemmas?