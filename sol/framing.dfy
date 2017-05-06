// Exercise 13
predicate sorted(a: array<int>)
  requires a != null
  reads a
{
  forall i, j :: 0 <= i < j < a.Length ==> a[i] < a[j]
}

predicate sorted_with_null(a: array<int>)
  reads a
{
  a != null && sorted(a)
}
