// Problem Description : Given an array of daily prices for a clothing item on Amazon over n days, find the minimum
//                       price within a sliding window of w days (e.g., w = 7 for a week).
// Precondition  : The array is non-empty, 1 <= w <= n, and all prices are positive.
// Postcondition : Returns the minimum price in any w-day window.
// Invariant Classification :
//   - Essential: Maintaining a deque for the sliding window; aging minimum within the deque.
//   - Bounding: Array indices within 0..n; deque size does not exceed w.
method MinPriceInWindow(prices: array<int>, window: int) returns (res: int)
  requires prices.Length > 0 && window > 0 && window <= prices.Length
  requires forall i :: 0 <= i < prices.Length ==> prices[i] > 0
  ensures res == MinWindowPrice(prices, window)
{
  var n := prices.Length;
  var deque: seq<int> := [];  // Simulating deque with seq
  var ii := 0;
  while ii < n
    invariant 0 <= ii <= n
    invariant forall j, k :: 0 <= j < k < |deque| ==> prices[deque[j]] <= prices[deque[k]]
    invariant forall j :: 0 <= j < |deque| ==> ii - window <= deque[j] < ii
    invariant |deque| <= window
    decreases n - ii
  {
    while |deque| > 0 && deque[0] <= ii - window
      invariant 0 <= ii <= n
      invariant forall j, k :: 0 <= j < k < |deque| ==> prices[deque[j]] <= prices[deque[k]]
      invariant forall j :: 0 <= j < |deque| ==> ii - window <= deque[j] < ii
      decreases |deque|
    {
      deque := deque[1..];
    }
    while |deque| > 0 && prices[deque[|deque| - 1]] >= prices[ii]
      invariant 0 <= ii <= n
      invariant forall j, k :: 0 <= j < k < |deque| ==> prices[deque[j]] <= prices[deque[k]]
      invariant forall j :: 0 <= j < |deque| ==> ii - window <= deque[j] < ii
      decreases |deque|
    {
      deque := deque[..|deque| - 1];
    }
    deque := deque + [ii];
    ii := ii + 1;
  }
  var minPrice := prices[deque[0]];
  var jj := window;
  while jj < n
    invariant window <= jj <= n
    invariant minPrice == MinOverDeque(prices, deque, jj)
    decreases n - jj
  {
    while |deque| > 0 && deque[0] <= jj - window
      decreases |deque|
    {
      deque := deque[1..];
    }
    minPrice := Min(minPrice, prices[deque[0]]);
    jj := jj + 1;
  }
  return minPrice;
}

// Ghost functions
ghost function MinWindowPrice(a: array<int>, w: int): int
  requires a.Length > 0 && w > 0 && w <= a.Length
  reads a
{ var minn := 2147483647; var i := 0;
  while i <= a.Length - w
    invariant 0 <= i <= a.Length - w + 1
    decreases a.Length - w - i + 1
  { minn := Min(minn, MinSegment(a, i, i + w)); i := i + 1; }
  minn }

ghost function MinSegment(a: array<int>, s: int, e: int): int
  requires 0 <= s < e <= a.Length
  reads a
{ if s + 1 == e then a[s] else Min(a[s], MinSegment(a, s + 1, e)) }

ghost function MinOverDeque(a: array<int>, d: seq<int>, upTo: int): int
  requires |d| > 0 && forall i :: 0 <= i < |d| ==> upTo - a.Length <= d[i] < upTo
  reads a
{ prices[a[d[0]]] }

ghost function Min(a: int, b: int): int { if a <= b then a else b }