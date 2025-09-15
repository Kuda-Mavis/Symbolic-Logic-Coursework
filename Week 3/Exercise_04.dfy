// Problem Description : Given two arrays - departure prices D (from city A to B, sorted by date/time)
//                       and return prices R (from B to A, sorted by date/time) - find the minimum cost
//                       of a round-trip where the return date/time is on or after the departure.
// Pre : Arrays non-empty, same length n, prices positive.
// Post : Result is min(D[i] + R[j]) for i <= j.
// Invariant Classification : Essential (uncoupling prefixes; aging minimum costs up to j); Bounding 
//                            (index <= n, costs positive).
method CheapestRoundTrip(depart: array<int>, ret: array<int>) returns (res: int)
  requires depart.Length == ret.Length > 0
  requires forall i :: 0 <= i < depart.Length ==> depart[i] > 0 && ret[i] > 0
  ensures res == MinRoundTripCost(depart, ret)
{
  var n := depart.Length;
  var minDep := new int[n + 1];
  minDep[0] := 0;
  var ii := 1;
  while ii <= n
    invariant 1 <= ii <= n + 1
    invariant forall k :: 0 <= k < ii ==> minDep[k] == MinPrefixDep(depart, k)
    decreases n + 1 - ii
  {
    minDep[ii] := Min(minDep[ii - 1], depart[ii - 1]);
    ii := ii + 1;
  }
  var minCost := 0;  // Track overall min
  var jj := 0;
  while jj < n
    invariant 0 <= jj <= n
    invariant minCost == MinOverReturns(depart, ret, jj)
    decreases n - jj
  {
    var thisCost := ret[jj] + minDep[jj + 1];  // Min dep for i <= jj
    if jj == 0 || thisCost < minCost {
      minCost := thisCost;
    }
    jj := jj + 1;
  }
  return minCost;
}

// Ghost functions
ghost function MinPrefixDep(a: array<int>, len: int): int
  requires 0 <= len <= a.Length
  reads a
{ if len == 0 then 0 else Min(MinPrefixDep(a, len - 1), a[len - 1]) }

ghost function MinRoundTripCost(d: array<int>, r: array<int>): int
  requires d.Length == r.Length > 0
  reads d, r
{ MinOverReturns(d, r, d.Length) }

ghost function MinOverReturns(d: array<int>, r: array<int>, upTo: int): int
  requires 0 <= upTo <= d.Length
  reads d, r
{ if upTo == 0 then 2147483647 else
    var this := r[upTo - 1] + MinPrefixDep(d, upTo);
    Min(this, MinOverReturns(d, r, upTo - 1)) }

ghost function Min(a: int, b: int): int { if a <= b then a else b }