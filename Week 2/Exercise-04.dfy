// Problem 4: Fast Power (Exponentiation by Squaring)
// Compute base^exp using exponentiation by squaring

method FastPower(base: int, exp: int) returns (result: int)
    requires exp >= 0
    ensures result == Power(base, exp)
{
    var x := base;
    var n := exp;
    result := 1;

    while n > 0
        invariant n >= 0                                     // exponent part never goes negative
        invariant result * Power(x, n) == Power(base, exp)  // decomposition of the power is preserved
        decreases n
    {
        if n % 2 == 1 {
            result := result * x;
        }
        x := x * x;
        n := n / 2;
    }
}

// Helper function
function Power(base: int, exp: int): int
    requires exp >= 0
{
    if exp == 0 then 1 else base * Power(base, exp - 1)
}

/*
    Explanation :

    Initialization :
    Before the loop starts, the result = 1, x = base, and n = exp. The invariants hold true because n >= 0 
    (by precondition), and again, the result * Power(x, n) == Power(base, exp) holds true initially as 
    1 * Power(base, exp) == Power(base, exp).

    Preservation :
    At the start of each iteration, the invariants are assumed to hold. The loop checks if n is odd :
        - If n % 2 == 1, result is multiplied by x.  
        - x is then squared, and n is halved (integer division).  
    This therefore preserves the key invariant result * Power(x, n) == Power(base, exp) because multiplying
    the result by x and halving n while squaring x continues to maintain the same total product (exponentiation
    decomposition). n >= 0 is preserved because halving a non-negative integer never produces a negative value.

    Termination :
    The loop stops when n == 0 and at this point, the invariant result * Power(x, n) == Power(base, exp) becomes
    result * Power(x, 0) == Power(base, exp), which simplifies to result * 1 == Power(base, exp). This gives that 
    the result == Power(base, exp) and matches with the postcondition, implying that the program correct.
*/