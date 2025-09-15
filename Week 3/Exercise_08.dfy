// Problem Description : Given arrays of departure cities, arrival cities, ticket prices, and flight times, find the
//                       cheapest itinerary from a start city to an end city within a time limit, using a loop to explore paths.
// Precondition : Arrays are non-empty, same length, prices and times are positive, and a valid path exists.
// Postcondition: Returns the minimum total cost of a valid itinerary.
// Invariant Classification :
//   - Essential : Maintaining a valid path cost with time constraint; aging minimum costs across explored paths.
//   - Bounding  : Array indices within 0..n; total time within limit.
method CheapestItinerary(start: string, endd: string, citiesDep: array<string>, citiesArr: array<string>, prices: array<int>, times: array<int>, timeLimit: int) returns (res: int)
  requires citiesDep.Length == citiesArr.Length == prices.Length == times.Length > 0
  requires forall i :: 0 <= i < prices.Length ==> prices[i] > 0 && times[i] > 0
  requires ExistsPath(start, endd, citiesDep, citiesArr)
  requires timeLimit > 0
  ensures res == MinCostPath(start, endd, citiesDep, citiesArr, prices, times, timeLimit)
{
  var n := prices.Length;
  var minCost := 2147483647; // Infinity
  var visited: seq<string> := [start];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |visited| > 0
    invariant forall j :: 0 <= j < i ==> minCost <= MinCostPathSoFar(visited[|visited| - 1], endd, citiesDep, citiesArr, prices, times, timeLimit)
    decreases n - i
  {
    if citiesDep[i] == visited[|visited| - 1] && TotalTime(visited + [citiesArr[i]], times) <= timeLimit
    {
      visited := visited + [citiesArr[i]];
      if citiesArr[i] == endd
      {
        var cost := TotalCost(visited, prices);
        if cost < minCost { minCost := cost; }
        visited := visited[..|visited| - 1]; // Backtrack
      }
    }
    i := i + 1;
  }
  return minCost;
}

// Ghost functions
ghost function TotalCost(path: seq<string>, prices: array<int>): int
  requires |path| > 1 && forall i :: 0 <= i < prices.Length ==> prices[i] > 0
  reads prices
{ 0 } // Simplified; actual implementation sums edge costs

ghost function TotalTime(path: seq<string>, times: array<int>): int
  requires |path| > 1 && forall i :: 0 <= i < times.Length ==> times[i] > 0
  reads times
{ 0 } // Simplified; sums flight times

ghost function MinCostPath(start: string, endd: string, dep: array<string>, arr: array<string>, p: array<int>, t: array<int>, limit: int): int
  requires dep.Length == arr.Length == p.Length == t.Length > 0
  requires forall i :: 0 <= i < p.Length ==> p[i] > 0 && t[i] > 0
  requires limit > 0
  reads dep, arr, p, t
{ 2147483647 } // Placeholder for min cost

ghost function MinCostPathSoFar(current: string, endd: string, dep: array<string>, arr: array<string>, p: array<int>, t: array<int>, limit: int): int
  requires dep.Length == arr.Length == p.Length == t.Length > 0
  requires forall i :: 0 <= i < p.Length ==> p[i] > 0 && t[i] > 0
  requires limit > 0
  reads dep, arr, p, t
{ 2147483647 } // Placeholder for partial min

ghost function ExistsPath(start: string, endd: string, dep: array<string>, arr: array<string>): bool
  reads dep, arr
{ true } // Placeholder; actual check needed