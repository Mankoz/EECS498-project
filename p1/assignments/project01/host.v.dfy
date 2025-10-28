//#title Host protocol
//#desc Define the host state machine here: message type, state machine for executing one
//#desc host's part of the protocol.

// See exercise01.dfy for an English design of the protocol.

include "network.t.dfy"
//#extract network.t.template solution network.t.dfy

module Host {
  import opened UtilitiesLibrary
  import opened HostIdentifiers
  import Network

  // Define your Message datatype here.
  datatype Message =
/*{*/
  | Grant(to: HostId, epoch: nat) // Populate this datatype.
/*}*/

  // Define your Host protocol state machine here.
  datatype Constants = Constants(numHosts: nat, myId:HostId) {
    // host constants coupled to DistributedSystem Constants:
    // DistributedSystem tells us our id so we can recognize inbound messages.
    ghost predicate Configure(numHosts: nat, id:HostId) {
      && this.numHosts == numHosts
      && this.myId == id
    }
  }

  datatype Variables = Variables(
/*{*/
    hasLock: bool,
    epoch: nat
/*}*/
  )

  ghost predicate Init(c:Constants, v:Variables) {
/*{*/
  if c.myId == 0 then v.hasLock && v.epoch == 1
  else !v.hasLock && v.epoch == 0
/*}*/
  }

/*{*/
  ghost predicate CanSendGrant(c:Constants, v:Variables, to:HostId, e:nat)
  {
    v.hasLock
    && ValidHostId(c.numHosts, to)
    && to != c.myId
    && e > v.epoch
  }

  ghost predicate CanReceiveGrant(v:Variables, e:nat)
  {
    e > v.epoch
  }
/*}*/
  // JayNF
  datatype Step =
/*{*/
    | Idle
    | SendGrant(to: HostId, e: nat)
    | RecvGrant(e: nat)
/*}*/

  ghost predicate NextStep(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps<Message>, step: Step) {
    match step
/*{*/
   case Idle =>
      v' == v
    case SendGrant(to, e) =>
      CanSendGrant(c, v, to, e)
      && v' == Variables(false, v.epoch)
    case RecvGrant(e) =>
      CanReceiveGrant(v, e)
      && v' == Variables(true, e)
/*}*/
  }

  ghost predicate Next(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps<Message>) {
    exists step :: NextStep(c, v, v', msgOps, step)
  }
}
