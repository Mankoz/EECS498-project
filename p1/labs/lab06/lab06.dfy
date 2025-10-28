datatype Constants = Constants(nodes: nat)
{
    ghost predicate WellFormed()
    {
        true
    }
}

datatype Variables = Variables(curr: nat, adj: seq<set<nat>>)
{
    ghost predicate WellFormed(c: Constants)
    {
        true
    }
}

ghost predicate Init(c: Constants, v: Variables)
{
    true
}

ghost predicate Walk(c: Constants, v: Variables, v': Variables, source: nat, target: nat)
{
    true
}

datatype Step = Walk(source: nat, target: nat)

ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step)
{
    match (step)
    {
        case Walk(source, target) => Walk(c, v, v', source, target)
    }
}

ghost predicate Next(c: Constants, v: Variables, v': Variables)
{
    exists step :: NextStep(c, v, v', step)
}

ghost predicate Safety(c: Constants, v: Variables)
{
    true
}

ghost predicate Inv(c: Constants, v: Variables)
{
    true
}

// Likely proves by itself
lemma InitImpliesInv(c: Constants, v: Variables)
    requires Init(c, v)
    ensures Inv(c, v)
{
}

// Likely proves by itself
lemma InvImpliesSafety(c: Constants, v: Variables)
    requires Inv(c, v)
    ensures Safety(c, v)
{
}

// Might not prove by itself
lemma NextPreservesInv(c: Constants, v:Variables, v': Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures Inv(c, v')
{
}
