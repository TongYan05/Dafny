// let's mess with the component parts of the following
//   - add a return type?
//   - add requires; add ensures
//   - remove requires ; remove ensures
//   - remove/add parameters
lemma simple(m:real, n:real)
  requires m <= n 
  requires n < m//两个条件互相冲突，所以无论ensures什么都是true
  ensures m + 1000.0 < m
{}

