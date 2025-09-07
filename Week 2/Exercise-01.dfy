// Problem 1: Simple Loop with Two Variables

method loop(n: int) returns (j: int)
    requires n >= 0
    ensures j == 2 * n
{
    var i := 0;
    j := 0;
    
   // Loop invariants
   while i < n
    invariant 0 <= i <= n           // According to the implied variable, i should always be between 0 and n
    invariant j == 2 * i            // According to the implied varibale, j should always be twice the value of i
    decreases n - i
{
    i := i + 1;
    j := j + 2;
}
}

/*
    Explanation :

    Initialization :
    Before the loop starts, i and j are set such that i = 0 and j = 0. The invariant j == 2 * i holds because 0 == 2 * 0. 
    The bound invariant 0 <= i <= n also holds, since i = 0 and n is non-negative.

    Preservation :
    At the start of each iteration, it has been assumed that the invariants hold. The loop then increases i by 1 
    and j by 2. If j was equal to 2 * i before, then after the update j becomes 2 * (i + 1), 
    which keeps the relationship true. Since the loop only runs while i < n, incrementing i by 1 
    still keeps i within 0 <= i <= n, hence both invariants remain valid.

    Termination :
    The loop stops when i == n. At this point, the invariant j == 2 * i which gives j == 2 * n. 
    This is exactly what the postcondition requires, so the program is correct.
*/
