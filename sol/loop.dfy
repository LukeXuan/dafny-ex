// Exercise 7
// Loop still verify
// Assertion failed

// Exercise 8
// This verifies if i <= n, which would always be satisfied since i equals 0 initially and n is a natural number
method m(n: nat)
{
  var i: int := 0;
  while i != n
    invariant 0 <= i <= n
  {
    i := i + 1;
  }
  assert i == n;
}

// Exercise 9 and 10
function fib(n: nat): nat
{
  if n == 0 then 0 else
    if n == 1 then 1 else
    fib(n - 1) + fib(n - 2)
}

method ComputeFib(n: nat) returns (b: nat)
  ensures b == fib(n)  // Do not change this postcondition
{
  // Change the method body to instead use c as described.
  // You will need to change both the initialization and the loop.
  var i: int := 0;
  var c: int := 1;
  b := 0;
  while i < n
    invariant 0 <= i <= n
    invariant c == fib(i + 1)
    invariant b == fib(i)
  {
    b, c := c, b + c;
    i := i + 1;
  }
}

// Exercise 11
method m_ex11()
{
  var i, n := 0, 20;
  while i != n
    invariant i <= n
    decreases n - i // Here fails without invariant, as Dafny know nothing about the boundness
  {
    i := i + 1;
  }
}
