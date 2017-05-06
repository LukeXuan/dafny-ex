method Find(a: array<int>, key: int) returns (index: int)
  requires a != null
  ensures 0 <= index ==> index < a.Length && a[index] == key
{
  // Can you write code that satisfies the postcondition?
  // Hint: you can do it with one statement.
  index := 0;
  while index < a.Length
    invariant 0 <= index <= a.Length
  {
    if a[index] == key {
      return;
    }
    index := index + 1;
  }

  index := -1;
}
