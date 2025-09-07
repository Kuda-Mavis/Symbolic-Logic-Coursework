// Problem 2: Integer Division (Quotient & Remainder)
// Computing the quotient and remainder of dividend/divisor

method IntegerDivision(dividend: int, divisor: int) returns (quotient: int, remainder: int)
    requires divisor > 0
    requires dividend >= 0
    ensures dividend == divisor * quotient + remainder
    ensures 0 <= remainder < divisor
{
    quotient := 0;
    remainder := dividend;

    while remainder >= divisor
        invariant dividend == divisor * quotient + remainder   // The dividend is correctly split into quotient * divisor + remainder
        invariant 0 <= remainder                               // The remainder never goes below 0 during the process
        invariant 0 <= quotient                                // The quotient never becomes negative, it only increases
        decreases remainder
    {
        quotient := quotient + 1;
        remainder := remainder - divisor;
    }
}

/*
    Explanation :

    Initialization :
    Before the loop starts, the quotient = 0 and the remainder = dividend. The invariant will be the
    dividend == divisor * quotient + remainder and this holds because the dividend == divisor * 0 + dividend.
    Additionally, the remainder is non-negative and since the dividend >= 0 (from the precondition), and the
    quotient is 0. Therefore, all the invariants are satisfied right at the beginning of the loop.

    Preservation :
    At the start of each iteration, the invariants are assumed to hold. The loop then increases 
    quotient by 1 and decreases the remainder by the divisor. If the relation of the 
    dividend == divisor * quotient + remainder was true before, it will remain true after the update, 
    since the divisor * (quotient + 1) + (remainder - divisor) this simplifies back to the dividend. 
    The remainder will remain non-negative because the loop will only run while the remainder >= divisor, 
    hence subtracting the divisor keeps it >= 0. The quotient also remains non-negative since it starts at 0 
    and only increases.

    Termination :
    The loop stops when the remainder < the divisor. At this point, the invariant which is the 
    dividend == divisor * quotient + remainder will still hold, and the exit condition guarantees 
    that 0 <= remainder < divisor. This therefore matches exactly with the postconditions, and can safely conclude
    that the program is correct.
*/
