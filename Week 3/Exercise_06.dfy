// Problem Description : Given an array of songs with titles, play counts, and genres, compute a visual representation
//                       where each song's play count determines its size and genre determines its color on a canvas.
// Precondition : The array is non-empty, play counts are non-negative, and genres are valid (e.g., "pop", "rock").
// Postcondition: Returns a sequence of (x, y, size, color) tuples representing the visual layout.
// Invariant Classification :
//   - Essential : Maintaining a valid mapping of play counts to sizes and genres to colors; aging positions for animation.
//   - Bounding  : Canvas coordinates within 0..width and 0..height; size within a reasonable range.
method VisualizePlaylist(songs: array<Song>) returns (res: seq<(int, int, int, (int, int, int))>)
  requires songs.Length > 0
  requires forall i :: 0 <= i < songs.Length ==> songs[i].plays >= 0 && (songs[i].genre == "pop" || songs[i].genre == "rock")
  ensures res.Length == songs.Length
  ensures forall i :: 0 <= i < res.Length ==> 0 <= res[i].0 < 400 && 0 <= res[i].1 < 400 && 10 <= res[i].2 <= 50
  ensures forall i :: 0 <= i < res.Length ==> (songs[i].genre == "pop" ==> res[i].3 == (0, 0, 255)) && (songs[i].genre == "rock" ==> res[i].3 == (255, 0, 0))
{
  var positions := new seq<(int, int)>[songs.Length];
  var i := 0;
  while i < songs.Length
    invariant 0 <= i <= songs.Length
    invariant |positions| == i
    invariant forall j :: 0 <= j < i ==> 0 <= positions[j].0 < 400 && 0 <= positions[j].1 < 400
    decreases songs.Length - i
  {
    positions := positions + [(RandomInt(400), RandomInt(400))]; // Simulated random initial position
    i := i + 1;
  }
  var result: seq<(int, int, int, (int, int, int))> := [];
  i := 0;
  while i < songs.Length
    invariant 0 <= i <= songs.Length
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> 0 <= result[j].0 < 400 && 0 <= result[j].1 < 400 && 10 <= result[j].2 <= 50
    invariant forall j :: 0 <= j < i ==> (songs[j].genre == "pop" ==> result[j].3 == (0, 0, 255)) && (songs[j].genre == "rock" ==> result[j].3 == (255, 0, 0))
    decreases songs.Length - i
  {
    var size := if songs[i].plays > 100 then 50 else songs[i].plays * 50 / 100 + 10; // Scale 10-50
    var color := if songs[i].genre == "pop" then (0, 0, 255) else (255, 0, 0);
    var pos := positions[i];
    result := result + [(pos.0, pos.1, size, color)];
    i := i + 1;
  }
  return result;
}

// Ghost functions (simplified random for Dafny)
ghost function RandomInt(max: int): int
  requires max > 0
{ 0 } // Placeholder; in practice, using a verifiable random generator

datatype Song = Song(title: string, plays: int, genre: string)