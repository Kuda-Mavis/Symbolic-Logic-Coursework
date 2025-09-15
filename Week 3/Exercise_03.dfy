// Problem Description : Given a sentence (array of English words) and a dictionary mapping English words
//                       to foreign words, find the minimum number of foreign words needed to translate the
//                       sentence. Each English word maps to exactly one foreign word, minimizing the total count.
// Precondition  : The sentence is non-empty, and the dictionary is valid.
// Postcondition : Returns the minimum number of foreign words required for translation.
// Invariant Classification :
//   - Essential: Uncoupling prefixes; aging minimum counts.
//   - Bounding: Array indices within valid range (0..length).
method MinTranslationWords(sentence: array<string>, dictionary: map<string, string>) returns (res: int)
  requires sentence.Length > 0
  requires forall w :: w in dictionary.Keys ==> dictionary[w] != null
  ensures res == MinTranslationCost(sentence, dictionary)
{
  var dp := new int[sentence.Length + 1];
  var ii := 0;
  while ii <= sentence.Length
    invariant 0 <= ii <= sentence.Length + 1
    invariant forall k :: 0 <= k <= ii ==> dp[k] == (if k == 0 then 0 else MinCostPrefix(sentence, k, dictionary))
    decreases sentence.Length + 1 - ii
  {
    dp[ii] := 2147483647; // Infinity
    if ii == 0 { dp[ii] := 0; }
    var jj := 0;
    while jj < ii
      invariant 0 <= jj <= ii
      invariant dp[ii] == MinOverJ(sentence, dictionary, ii, jj)
      decreases ii - jj
    {
      if jj > 0 && dp[jj] != 2147483647 {
        var word := Concatenate(sentence, jj, ii);
        if word in dictionary {
          var cost := dp[jj] + |dictionary[word]|;
          if cost < dp[ii] {
            dp[ii] := cost;
          }
        }
      }
      jj := jj + 1;
    }
    ii := ii + 1;
  }
  return dp[sentence.Length];
}

// Ghost helpers
ghost function Concatenate(a: array<string>, s: int, e: int): string
  requires 0 <= s <= e <= a.Length
  reads a
{ if s == e then "" else a[s] + Concatenate(a, s + 1, e) }

ghost function MinCostPrefix(a: array<string>, len: int, d: map<string, string>): int
  requires 0 <= len <= a.Length
  reads a, d
{ if len == 0 then 0 else MinOverJ(a, d, len, 0) }

ghost function MinOverJ(a: array<string>, d: map<string, string>, endd: int, upTo: int): int
  requires 0 <= upTo <= endd <= a.Length
  reads a, d
{ if upTo == endd then 2147483647 else
    var word := Concatenate(a, upTo, endd);
    var prev := MinOverJ(a, d, endd, upTo + 1);
    if upTo > 0 && word in d then Min(prev, MinCostPrefix(a, upTo, d) + |d[word]|) else prev }

ghost function Min(a: int, b: int): int { if a <= b then a else b }

ghost function MinTranslationCost(a: array<string>, d: map<string, string>): int
  reads a, d
{ MinCostPrefix(a, a.Length, d) }