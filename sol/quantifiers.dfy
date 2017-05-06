// Exercise 12

method FindMax(a: array<int>) returns (i: int)
  requires a != null && a.Length >= 1
  ensures 0 <= i < a.Length
  ensures forall k :: 0 <= k < a.Length ==> a[k] <= a[i]
{
  // Ugly solution :(
  i := 0;
  var j := 1;
  while j < a.Length
    invariant 0 <= i < j <= a.Length
    invariant forall k :: 0 <= k < j ==> a[k] <= a[i]
  {
    if a[j] > a[i] {
      i := j;
    }
    j := j + 1;
  }
}
