datatype Direction = North | South | East | West

datatype Variables = Variables(x: int, y: int, dir: Direction)

ghost predicate Init(v: Variables){
    true
}

ghost predicate MoveEast(v: Variables, v': Variables){
    true
}

ghost predicate MoveWest(v: Variables, v': Variables){
    true
}

ghost predicate MoveNorth(v: Variables, v': Variables){
    true
}

ghost predicate MoveSouth(v: Variables, v': Variables){
    true
}

ghost predicate TurnEast(v: Variables, v': Variables)
{
    true
}

ghost predicate TurnWest(v: Variables, v': Variables)
{
    true
}

ghost predicate TurnNorth(v: Variables, v': Variables)
{
    true
}

ghost predicate TurnSouth(v: Variables, v': Variables)
{
    true
}

ghost predicate Warp(v: Variables, v': Variables)
{
    true
}

datatype Step =
    | MoveEast
    | MoveNorth
    | MoveSouth
    | MoveWest
    | TurnEast
    | TurnNorth
    | TurnSouth
    | TurnWest
    | Warp

ghost predicate NextStep(v: Variables, v': Variables, step: Step)
{
    match (step)
    {
        case MoveEast => MoveEast(v, v')
        case MoveNorth => MoveNorth(v, v')
        case MoveSouth => MoveSouth(v, v')
        case MoveWest => MoveWest(v, v')
        case TurnEast => TurnEast(v, v')
        case TurnNorth => TurnNorth(v, v')
        case TurnSouth => TurnSouth(v, v')
        case TurnWest => TurnWest(v, v')
        case Warp => Warp(v, v')
    }
}

ghost predicate Next(v: Variables, v': Variables)
{
    exists step :: NextStep(v, v', step)
}

ghost predicate Safety(v: Variables)
{
    true
}

ghost predicate Inv(v: Variables)
{
    true
}

// Might not need proof
lemma InitImpliesInv(v: Variables)
    requires Init(v)
    ensures Inv(v)
{
}

lemma InvImpliesSafety(v: Variables)
    requires Inv(v)
    ensures Safety(v)
{
}

lemma NextPreservesInv(v:Variables, v': Variables)
    requires Inv(v)
    requires Next(v, v')
    ensures Inv(v')
{
}