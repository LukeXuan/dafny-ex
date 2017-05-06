// Exercise 4
function max_ex4(a: int, b: int): int {
  if a > b then a else b
}

method Testing_ex4() {
  assert max_ex4(3, 2) == 3;
}

// Exercise 5
function method max_ex5(a: int, b: int): int {
  if a > b then a else b
}

method Testing_ex5() {
  var m := max_ex5(3, 2);
  assert m == 3;
}

// Exercise 6
function method abs_ex6(x: int): int
{
  if x < 0 then -x else x
}

method Abs_ex6(x: int) returns (y: int)
  ensures y == abs_ex6(x)
{
  // Then change this body to also use abs.
  return abs_ex6(x);
}

