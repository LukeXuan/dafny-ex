predicate is_heap(a: array<int>)
  requires a != null
  reads a
{
  forall i :: 0 < i < a.Length ==> a[i] <= a[i / 2]
}

method swap(a: array<int>, i: int, j: int)
  modifies a
  requires a != null
  requires 0 <= i < a.Length
  requires 0 <= j < a.Length
  ensures a[i] == old(a[j])
  ensures a[j] == old(a[i])
  ensures forall k :: 0 <= k < a.Length && k != i && k != j ==> a[k] == old(a[k])
{
  var tmp := a[i];
  a[i] := a[j];
  a[j] := tmp;
}

method extend(src: array<int>, len: nat) returns (dst: array<int>)
  requires src != null
  ensures dst != null
  ensures dst.Length == src.Length + len
  ensures forall k :: 0 <= k < src.Length ==> dst[k] == src[k]
  ensures fresh(dst)
{
  dst := new int[src.Length + len];
  var i := 0;
  while i < src.Length
    invariant 0 <= i <= src.Length
    invariant forall k :: 0 <= k < i ==> dst[k] == src[k]
  {
    dst[i] := src[i];
    i := i + 1;
  }
}

method heap_push(heap: array<int>, element: int) returns (new_heap: array<int>)
  requires heap != null
  requires is_heap(heap)
  requires element !in heap[..]
  ensures new_heap != null
  ensures is_heap(new_heap)
  ensures new_heap.Length == heap.Length + 1
  ensures forall e :: e in heap[..] ==> e in new_heap[..]
  ensures element in new_heap[..]
{
  new_heap := extend(heap, 1);
  new_heap[heap.Length] := element;
  var i := heap.Length;
  assert forall e :: e in heap[..] ==> e in new_heap[..heap.Length];
  while i > 0
    invariant 0 <= i < new_heap.Length
    invariant forall k :: 0 <= k < new_heap.Length && k / 2 == i ==> new_heap[k] <= new_heap[k / 2 / 2]
    invariant forall k :: (0 <= k < new_heap.Length && k != i) ==> new_heap[k] <= new_heap[k / 2]
    invariant forall e :: e in heap[..] ==> e in new_heap[..]
    invariant element in new_heap[..]
  {
    if (new_heap[i] >= new_heap[i / 2]) {
      swap(new_heap, i, i / 2);
    }
    i := i / 2;
  }
}
