predicate is_heap(a: array<int>)
  requires a != null
  reads a
{
  forall i :: 1 < i < a.Length ==> a[i] <= a[i / 2]
}

lemma HeapTop(a: array<int>)
  requires a != null
  requires is_heap(a)
  requires a.Length > 1
  ensures forall k :: 2 <= k < a.Length ==> a[k] <= a[1]
{
  var i := 2;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 2 <= k < i ==> a[k] <= a[1]
  {
    var j := i;
    while j > 1
      invariant a[i] <= a[j];
      invariant j > 0;
    {
      j := j / 2;
    }
    i := i + 1;
  }
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

method slice(src: array<int>, len: nat) returns (dst: array<int>)
  requires src != null
  requires src.Length >= len
  ensures dst != null
  ensures dst.Length == len
  ensures forall k :: 0 <= k < len ==> dst[k] == src[k]
  ensures fresh(dst)
{
  dst := new int[len];
  var i := 0;
  while i < len
    invariant 0 <= i <= len
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
  ensures fresh(new_heap)
{
  new_heap := extend(heap, 1);
  new_heap[heap.Length] := element;
  var i := heap.Length;
  assert forall e :: e in heap[..] ==> e in new_heap[..heap.Length];
  while i > 1
    invariant 0 <= i < new_heap.Length
    invariant forall k :: 3 < k < new_heap.Length && k / 2 == i ==> new_heap[k] <= new_heap[k / 2 / 2]
    invariant forall k :: (1 < k < new_heap.Length && k != i) ==> new_heap[k] <= new_heap[k / 2]
    invariant forall e :: e in heap[..] ==> e in new_heap[..]
    invariant element in new_heap[..]
  {
    if (new_heap[i] >= new_heap[i / 2]) {
      swap(new_heap, i, i / 2);
    }
    i := i / 2;
  }
}

method heap_pop(heap: array<int>) returns (new_heap: array<int>, element: int)
  requires heap != null
  requires heap.Length > 1
  requires is_heap(heap)
  ensures new_heap != null
  ensures element in heap[..]
  ensures heap.Length == new_heap.Length + 1
  ensures is_heap(new_heap)
  ensures fresh(new_heap)
  ensures forall e :: e != element && e in heap[..] ==> e in new_heap[..]
  ensures forall k :: 1 <= k < new_heap.Length ==> new_heap[k] <= element
{
  var temp := extend(heap, 0);
  HeapTop(temp);
  element := heap[1];
  swap(temp, 1, temp.Length - 1);
  new_heap := slice(temp, temp.Length - 1);
  assert forall k :: 1 <= k < new_heap.Length ==> new_heap[k] <= element;
  assert forall e :: e != element && e in temp[..temp.Length] ==> e in heap[..];
  var i := 1;
  while i * 2 < new_heap.Length
    invariant 1 <= i
    invariant forall e :: e != element && e in heap[..] ==> e in new_heap[..]
    invariant forall k :: 1 < k < new_heap.Length && k / 2 != i ==> new_heap[k] <= new_heap[k / 2]
    invariant forall k :: 3 < k < new_heap.Length && k / 2 == i ==> new_heap[k] <= new_heap[k / 2 / 2]
    invariant forall k :: 1 <= k < new_heap.Length ==> new_heap[k] <= element
  {
    if (i * 2 + 1 == new_heap.Length) {
      if (new_heap[i] < new_heap[i * 2]) {
        swap(new_heap, i, i * 2);
      }
      i := i * 2;
    } else {
      if (new_heap[i] >= new_heap[i * 2] && new_heap[i] >= new_heap[i * 2 + 1]) {
        break;
      }
      else {
        if (new_heap[2 * i] > new_heap[2 * i + 1]) {
          swap(new_heap, i, 2 * i);
          i := i * 2;
        }
        else {
          swap(new_heap, i, 2 * i + 1);
          i := i * 2 + 1;
        }
      }
    }
  }
}
