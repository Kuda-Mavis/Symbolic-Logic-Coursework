// Problem 5: Reversing a Number

method ReverseNumber(n: int) returns (rev: int)
    requires n >= 0
    ensures rev == ReverseDigits(n)
{
    rev := 0;
    var num := n;
    
    while num > 0
        invariant rev >= 0                                     //  The reversed number is non-negative
        invariant num >= 0                                     // The remaining number is non-negative
        invariant rev * Power(10, NumDigits(num)) + num  == n   // rev and num together represent the original number n
        decreases num   
    {
        var digit := num % 10;
        rev := rev * 10 + digit;
        num := num / 10;
    }

}

// Helper function to define what "reversed" means
function ReverseDigits(n: int): int
    requires n >= 0
{
    if n < 10 then n else (n % 10) * Power(10, NumDigits(n) - 1) + ReverseDigits(n / 10)
}

// Helper function to count digits
function NumDigits(n: int): int
    requires n >= 0
{
    if n < 10 then 1 else 1 + NumDigits(n / 10)
}

// Helper function for power (needed for ReverseDigits)
function Power(base: int, exp: int): int
    requires exp >= 0
{
    if exp == 0 then 1 else base * Power(base, exp - 1)
}

/*
    Explanation :

    Initialization :
    Before the loop starts, rev = 0 and num = n. The invariants hold because rev >= 0 (0 is non-negative), 
    num >= 0 (since n >= 0 by precondition), and rev * Power(10, NumDigits(num)) + num == n holds because 
    0 * Power(10, NumDigits(n)) + n == n.

    Preservation :
    At the start of each iteration, the invariants are assumed to hold. The loop extracts the last digit 
    of num and appends it to rev:
        - rev := rev * 10 + digit
        - num := num / 10
    This therefore preserves rev >= 0 because rev and digit are non-negative. num >= 0 is preserved because
    integer division by 10 of a non-negative number remains non-negative.The key invariant 
    rev * Power(10, NumDigits(num)) + num == n which also holds after the update, because the new rev and new num
    still represent the original number n when combined.

    Termination :
    The loop stops when num == 0. At this point, the invariant rev * Power(10, NumDigits(num)) + num == n 
    becomes rev * Power(10, 0) + 0 == n, which simplifies to rev == n. This matches exactly with the postcondition
    rev == ReverseDigits(n), so the program is correct.
*/
