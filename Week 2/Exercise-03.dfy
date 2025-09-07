// Problem 3: GCD Calculation
// Computing the greatest common divisor of two positive integers a and b

method GCD(a: int, b: int) returns (gcd: int)
    requires a > 0 && b > 0
    ensures gcd > 0
    ensures a % gcd == 0 && b % gcd == 0
    ensures forall d :: d > 0 && a % d == 0 && b % d == 0 ==> d <= gcd
{
    var x := a;
    var y := b;

    while y != 0
        invariant x > 0            // x always remains positive
        invariant y >= 0           // y never becomes negative
        decreases y
    {
        var temp := y;
        y := x % y;
        x := temp;
    }

    gcd := x;
}

/*
    Explanation :

    Initialization :
    Before the loop starts, x = a and y = b. From the preconditions, both are positive, hence x > 0 
    and y >= 0 hold. There exists a greatest common divisor of x and y because x and y are copies of
    a and b.

    Preservation :
    At the start of each iteration, the invariants x > 0 and y >= 0 are assumed to hold. The loop updates
    x and y by setting x := y and y := x % y. Since the Euclidean algorithm preserves the greatest common
    divisor, the final x after the loop will be the GCD of the original a and b. The invariant x > 0 continues
    to hold because x is always assigned a positive value from y or the modulo operation. The invariant y >= 0
    continues to hold because modulo of non-negative numbers is non-negative. Therefore, the loop preserves the
    conditions needed for the postcondition: gcd > 0, a % gcd == 0, b % gcd == 0, and the maximality of gcd.

    Termination :
    The loop stops when y == 0. At this point, x contains the GCD of the original a and b. Assigning gcd := x 
    ensures that gcd > 0, divides both a and b, and is the largest number with this property, thereby 
    satisfying all postconditions.
*/


