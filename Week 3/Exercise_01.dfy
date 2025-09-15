// Problem Description : Given an array of songs (each with a play count), sort the array in descending
//                      order of play counts using insertion sort.
// Precondition  : The array is non-empty, and all play counts are non-negative.
// Postcondition : The array is sorted in descending order by play counts. The sort is stable: songs with
//                 equal play counts maintain their original relative order.
// Invariant Classification : 
//   - Essential : Term dropping (reduces full sort to the sorted prefix);
//                Constant relaxation (prefix gradually sorted descending).
//   - Bounding  : Array indices within 0..n; play counts non-negative.
datatype Song = Song(name: string, plays: int)

method SortSongsByPlays(songs: array<Song>)
  modifies songs
  requires songs.Length > 0
  requires forall i :: 0 <= i < songs.Length ==> songs[i].plays >= 0
  ensures forall i, j :: 0 <= i < j < songs.Length ==> songs[i].plays >= songs[j].plays
  ensures Multiset(songs[..]) == old(Multiset(songs[..]))
{
  var ii := 1;
  while ii < songs.Length
    invariant 1 <= ii <= songs.Length
    invariant forall p, q :: 0 <= p < q < ii ==> songs[p].plays >= songs[q].plays
    invariant Multiset(songs[0..ii]) == old(Multiset(songs[0..ii]))
    decreases songs.Length - ii
  {
    var key := songs[ii];
    var jj := ii - 1;
    while jj >= 0 && songs[jj].plays < key.plays
      invariant -1 <= jj < ii
      invariant forall k :: jj + 1 <= k < ii ==> songs[k].plays <= key.plays
      invariant Multiset(songs[0..ii+1]) == Multiset(old(songs[0..ii]) + [key])
      decreases jj
    {
      songs[jj + 1] := songs[jj];
      jj := jj - 1;
    }
    songs[jj + 1] := key;
    ii := ii + 1;
  }
}
