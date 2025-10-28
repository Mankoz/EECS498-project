// Write a state machine spec representing the factory floor and robot.
datatype Color = Red | Blue

datatype Constants = Constants()
datatype Variables = Variables()

// Define any helper predicates/functions as needed.



ghost predicate Init(c: Constants, v: Variables)
{
    // Fill in here
    true
}

ghost predicate PickUp(c: Constants, v: Variables, v': Variables, stack_index: nat)
{
    // Fill in here
    true
}

ghost predicate Drop(c: Constants, v: Variables, v': Variables, stack_index: nat)
{
    // Fill in here
    true
}

ghost predicate Deliver(c: Constants, v: Variables, v': Variables)
{
    // Fill in here
    true
}

// Write out the JNF 



ghost predicate Next(c: Constants, v: Variables, v': Variables)
{
    true
}




ghost predicate Safety(c: Constants, v: Variables)
{
    // Fill in the safety condition.
    true
}

// Should prove by itself!
lemma SafetyProof()
    ensures forall c, v :: Init(c, v) ==> Safety(c, v)
    ensures forall c, v, v' :: Safety(c, v) && Next(c, v, v') ==> Safety(c, v')
{
}
