// Problem Description : Given an array of movies (each with a title and rating), find the movie
//                       with the k-th highest rating using quickselect.
// Precondition  : The array is non-empty, 1 <= k <= n, and all ratings are positive.
// Postcondition : Returns the movie with the k-th highest rating. Ties are broken lexicographically
//                 by title.
datatype Movie = Movie(title: string, rating: int)

method KthHighestMovie(movies: array<Movie>, kk: int) returns (res: Movie)
  modifies movies
  requires movies.Length > 0 && 1 <= kk <= movies.Length
  requires forall i :: 0 <= i < movies.Length ==> movies[i].rating > 0
  ensures res.rating == KthHighestRating(old(movies[..]), kk)
{
  var lo := 0;
  var hi := movies.Length - 1;
  while lo < hi
    invariant 0 <= lo <= hi < movies.Length
    invariant Multiset(movies[lo..hi+1]) == old(Multiset(movies[lo..hi+1]))
    invariant KthInSubarray(movies, lo, hi, kk)
    decreases hi - lo
  {
    var piv := Partition(movies, lo, hi);
    if piv == movies.Length - kk {
      return movies[piv];
    } else if piv > movies.Length - kk {
      hi := piv - 1;
    } else {
      lo := piv + 1;
    }
  }
  return movies[lo];
}

method Partition(movies: array<Movie>, lo: int, hi: int) returns (piv: int)
  modifies movies
  requires 0 <= lo <= hi < movies.Length
  ensures lo <= piv <= hi
  ensures forall i :: lo <= i < piv ==> movies[i].rating <= movies[piv].rating
  ensures forall i :: piv < i <= hi ==> movies[i].rating > movies[piv].rating
  ensures Multiset(movies[lo..hi+1]) == old(Multiset(movies[lo..hi+1]))
{
  var pivot := movies[hi];
  var ii := lo;
  var jj := lo;
  while jj < hi
    invariant lo <= ii <= jj <= hi
    invariant forall k :: lo <= k < ii ==> movies[k].rating <= pivot.rating
    invariant forall k :: ii <= k < jj ==> movies[k].rating > pivot.rating
    decreases hi - jj
  {
    if movies[jj].rating <= pivot.rating {
      Swap(movies, ii, jj);
      ii := ii + 1;
    }
    jj := jj + 1;
  }
  Swap(movies, ii, hi);
  return ii;
}

method Swap(movies: array<Movie>, i: int, j: int)
  modifies movies
  requires 0 <= i < movies.Length && 0 <= j < movies.Length
  ensures movies[i] == old(movies[j]) && movies[j] == old(movies[i])
  ensures forall k :: k != i && k != j ==> movies[k] == old(movies[k])
{
  var temp := movies[i];
  movies[i] := movies[j];
  movies[j] := temp;
}
