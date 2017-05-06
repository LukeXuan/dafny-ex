include "conditions.dfy"

// Exercise 1
method Testing() {
  var m := Max(2, 3);
  assert m == 3;
}

// Exercise 2
method Abs_ex2(x: int) returns (y: int)
  requires 0 > x
  ensures 0 <= y
  ensures 0 <= x ==> x == y
  ensures x < 0 ==> y == -x
{
  return -x;
}

// Exercise 3
method Abs_ex3_1(x: int) returns (y: int)
  requires 0 > x
  requires -1 == x
  ensures 0 <= y
  ensures 0 <= x ==> x == y
  ensures x < 0 ==> y == -x
{
  return x+2;
}

method Abs_ex3_2(x: int) returns (y: int)
  requires 0 > x
  requires false
  ensures 0 <= y
  ensures 0 <= x ==> x == y
  ensures x < 0 ==> y == -x
{
  return x+1;
}
