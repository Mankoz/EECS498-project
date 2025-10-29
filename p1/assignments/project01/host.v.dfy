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
  ghost predicate SendGrant(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps<Message>, to:HostId)
  {
    && v.hasLock
    && v' == v.(hasLock := false, epoch := v.epoch)
    && 0 <= to < c.numHosts
    && to != c.myId
    && msgOps.send == Some(Grant(to, v.epoch))
    && msgOps.recv == None
  }

  ghost predicate ReceiveGrant(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps<Message>)
  {
    && msgOps.recv.Some?
    && (var grant := msgOps.recv.value;
       && grant.to == c.myId
       && grant.epoch > v.epoch
       && !v.hasLock
       && v' == v.(hasLock := true, epoch := grant.epoch + 1))
    && msgOps.send == None
  }
/*}*/
  // JayNF
  datatype Step =
/*{*/
    | SendGrantStep(to: HostId)
    | ReceiveGrantStep
/*}*/

  ghost predicate NextStep(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps<Message>, step: Step) {
    match step
/*{*/
  case SendGrantStep(to) => SendGrant(c, v, v', msgOps, to)
  case ReceiveGrantStep => ReceiveGrant(c, v, v', msgOps)
/*}*/
  }

  ghost predicate Next(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps<Message>) {
    exists step :: NextStep(c, v, v', msgOps, step)
  }
}
