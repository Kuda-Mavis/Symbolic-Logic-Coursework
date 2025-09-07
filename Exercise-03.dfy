method Main () { 
// Learning to compare using "if " 
var x : int := 10;

if x > 15 {
   print x; print " is greater than 15!";   
} else { 
    print x; print " is less than 15!";   
}


// Learning to loop using " while "
var y: int := 1;  // This is the start value

// Looping until we reach 5
while y <= 5
    decreases 5 - y  // This statement here then informs Dafny that our code has to end eventually
{
    print y; y := y + 1;      // increment y so the loop progresses
}

}