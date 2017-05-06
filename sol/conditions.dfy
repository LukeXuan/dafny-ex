method Max(a: int, b: int) returns (c: int)
  ensures c >= a
  ensures c >= b
  ensures a == c || b == c
{
  if (a > b) {
    return a;
  }
  else {
    return b;
  }
}
