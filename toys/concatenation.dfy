method concat<T>(fst: array<T>, snd: array<T>) returns (res: array<T>)
  requires fst != null
  requires snd != null
  ensures res != null
  ensures res[..] == fst[..] + snd[..]
  ensures fresh(res)
{
  res := new T[fst.Length + snd.Length];
  var i := 0;
  while (i < fst.Length + snd.Length)
    invariant 0 <= i <= fst.Length + snd.Length
    invariant forall k :: 0 <= k < i && 0 <= k < fst.Length ==> res[k] == fst[k]
    invariant forall k :: fst.Length <= k < i ==> res[k] == snd[k - fst.Length]
  {
    if (i < fst.Length) {
      res[i] := fst[i];
    }
    else {
      res[i] := snd[i - fst.Length];
    }
    i := i + 1;
  }
}
