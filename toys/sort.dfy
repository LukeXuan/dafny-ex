method swap(arr: array<int>, i: int, j: int)
  requires arr != null
  requires 0 <= i <= j < arr.Length
  modifies arr
  ensures arr[i] == old(arr[j])
  ensures arr[j] == old(arr[i])
  ensures forall k :: 0 <= k < arr.Length && k != i && k != j ==> arr[k] == old(arr[k])
  ensures forall k, l :: 0 <= k <= i && j < l <= arr.Length ==> multiset(arr[k..l]) == old(multiset(arr[k..l]))
{
  var temp := arr[i];
  arr[i] := arr[j];
  arr[j] := temp;
}

method partition(arr: array<int>, pivot : int, begin: int, end: int) returns (smaller: int, larger: int)
  requires arr != null
  modifies arr
  requires 0 <= begin <= pivot < end <= arr.Length
  ensures begin <= smaller < larger <= end
  ensures forall i :: begin <= i < smaller ==> arr[i] < arr[smaller]
  ensures forall i :: smaller <= i < larger ==> arr[i] == arr[smaller]
  ensures forall i :: larger <= i < end ==> arr[i] > arr[smaller]
  requires forall i, j :: 0 <= i < begin && begin <= j < end ==> arr[i] < arr[j]
  requires forall i, j :: end <= i < arr.Length && begin <= j < end ==> arr[i] > arr[j]
  ensures forall i, j :: 0 <= i < begin && begin <= j < end ==> arr[i] < arr[j]
  ensures forall i, j :: end <= i < arr.Length && begin <= j < end ==> arr[i] > arr[j]
  ensures forall i :: 0 <= i < begin || end <= i < arr.Length ==> arr[i] == old(arr[i])
  ensures old(multiset(arr[begin..end])) == multiset(arr[begin..end])
  ensures forall k, l :: 0 <= k <= begin && end <= l <= arr.Length ==> multiset(arr[k..l]) == old(multiset(arr[k..l]))
{
  var i := begin + 1;

  var temp := arr[pivot];
  arr[pivot] := arr[begin];
  arr[begin] := temp;
  var j := begin;
  var k := begin + 1;

  while (i < end)
    invariant begin < i <= end
    invariant begin <= j < k <= i
    invariant forall l :: begin <= l < j ==> arr[l] < arr[j]
    invariant forall l :: j <= l < k ==> arr[l] == arr[j]
    invariant forall l :: k <= l < i ==> arr[l] > arr[j]
    invariant forall i, j :: 0 <= i < begin && begin <= j < end ==> arr[i] < arr[j]
    invariant forall i, j :: end <= i < arr.Length && begin <= j < end ==> arr[i] > arr[j]
    invariant forall i :: 0 <= i < begin || end <= i < arr.Length ==> arr[i] == old(arr[i])
    invariant forall k, l :: 0 <= k <= begin && end <= l <= arr.Length ==> multiset(arr[k..l]) == old(multiset(arr[k..l]))
  {
    if (arr[i] < arr[j]) {
      swap(arr, j, i);
      swap(arr, k, i);
      j := j + 1;
      k := k + 1;
    }
    else if (arr[i] == arr[j]) {
      swap(arr, k, i);
      k := k + 1;
    }
    i := i + 1;
  }

  smaller := j;
  larger := k;
}

method sort_aux(arr: array<int>, begin: int, end: int)
  requires arr != null
  modifies arr
  decreases end - begin
  requires 0 <= begin < end <= arr.Length
  requires forall i, j :: 0 <= i < begin && begin <= j < end ==> arr[i] < arr[j]
  requires forall i, j :: end <= i < arr.Length && begin <= j < end ==> arr[i] > arr[j]
  ensures forall i, j :: 0 <= i < begin && begin <= j < end ==> arr[i] < arr[j]
  ensures forall i, j :: end <= i < arr.Length && begin <= j < end ==> arr[i] > arr[j]
  ensures forall i :: 0 <= i < begin || end <= i < arr.Length ==> arr[i] == old(arr[i])
  ensures forall k, l :: 0 <= k <= begin && end <= l <= arr.Length ==> multiset(arr[k..l]) == old(multiset(arr[k..l]))
  ensures forall i :: begin <= i < end - 1 ==> arr[i] <= arr[i + 1]
{
  if (arr.Length == 0) {
    return;
  }
  var backup := arr[..];
  var smaller, larger := partition(arr, begin, begin, end);
  if (begin < smaller) {
    var backup := arr[..];
    sort_aux(arr, begin, smaller);
  }
  if (larger < end) {
    var backup := arr[..];
    sort_aux(arr, larger, end);
  }
}

lemma sequence_boundary_elimination(s: seq<int>)
  ensures s[0..|s|] == s[..]

method sort(arr: array<int>)
  requires arr != null
  modifies arr
  ensures forall i :: 0 <= i < arr.Length - 1 ==> arr[i] <= arr[i + 1]
  ensures multiset(arr[..]) == old(multiset(arr[..]))
{
  if (arr.Length == 0) {
    return;
  }
  sort_aux(arr, 0, arr.Length);
  sequence_boundary_elimination(arr[..]);
  sequence_boundary_elimination(old(arr[..]));
}
