// Problem Description : Given an array of movie-recipe pairs (movie title and ingredients list), compute a sequence
//                       of recipes where each is linked to a plot twist, ensuring ingredient counts are valid.
// Precondition : The array is non-empty, each movie has a unique title, and ingredient counts are positive.
// Postcondition: Returns a sequence of (movie, recipe, twist) tuples with valid ingredient sums.
// Invariant Classification :
//   - Essential : Maintaining a valid recipe construction with plot twist integration; aging recipe completeness.
//   - Bounding  : Ingredient counts within a reasonable range; array indices within 0..n.
method GenerateMovieRecipes(movies: array<(string, seq<string>)>) returns (res: seq<(string, seq<string>, string)>)
  requires movies.Length > 0
  requires forall i, j :: 0 <= i < j < movies.Length ==> movies[i].0 != movies[j].0
  requires forall i :: 0 <= i < movies.Length ==> forall ing :: ing in movies[i].1 ==> |ing| > 0
  ensures res.Length == movies.Length
  ensures forall i :: 0 <= i < res.Length ==> |res[i].1| == |movies[i].1| && TotalIngredients(res[i].1) > 0
{
  var result: seq<(string, seq<string>, string)> := [];
  var i := 0;
  while i < movies.Length
    invariant 0 <= i <= movies.Length
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> |result[j].1| == |movies[j].1| && TotalIngredients(result[j].1) > 0
    decreases movies.Length - i
  {
    var movie := movies[i].0;
    var ingredients := movies[i].1;
    var twist := if movie == "Star Wars" then "Surprise chili kick" else if movie == "Inception" then "Hidden lemon filling" else "Unexpected flavor";
    result := result + [(movie, ingredients, twist)];
    i := i + 1;
  }
  return result;
}

// Ghost functions
ghost function TotalIngredients(ings: seq<string>): int
  reads ings
{ |ings| }