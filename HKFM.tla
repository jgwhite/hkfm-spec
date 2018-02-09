-------------------------------- MODULE HKFM --------------------------------
EXTENDS Integers, Sequences
CONSTANTS Client, Song
VARIABLES inbox, state
-----------------------------------------------------------------------------
(***************************************************************************)
(* Type definitions (kinda sorta) and other useful stuff...                *)
(***************************************************************************)

(***************************************************************************)
(* There are various places where we want to refer to all variables at     *)
(* once, so it's useful to define a vars tuple.                            *)
(***************************************************************************)

vars == <<inbox, state>>

(***************************************************************************)
(* The constant Client is the set of all clients, represented however      *)
(* we want. It's defined externally, in the model.                         *)
(*                                                                         *)
(* We define Node to be the set of all nodes in the system, including the  *)
(* server. We don't care how the server is represented, only that it       *)
(* doesn't clash with any of the clients. We use the TLA+ CHOOSE operator  *)
(* to express this.                                                        *)
(***************************************************************************)

Server == CHOOSE x : x \notin Client
Node   == Client \cup {Server}

(***************************************************************************)
(* These terms all relate to the playhead. A playhead has two fields:      *)
(*                                                                         *)
(* i: the current track in the playlist                                    *)
(* t: the number of seconds into that track                                *)
(*                                                                         *)
(* When i = -1 it means we're not playing anything.                        *)
(*                                                                         *)
(* Every node has a State consisting of two fields:                        *)
(*                                                                         *)
(* playlist: a sequence of songs from the constant set Song                *)
(* playhead: as described above                                            *)
(***************************************************************************)

Idx       == Nat \cup {-1}
Playlist  == Seq(Song)
Playhead  == [i : Idx, t : Nat]
Stopped   == [i |-> -1, t |-> 0]
State     == [playlist : Playlist, playhead : Playhead]
InitState == [playlist |-> <<>>, playhead |-> Stopped]

(***************************************************************************)
(* Clients send "add", "seek", and "skip" messages to the server and       *)
(* the server sends "sync" messages to all clients whenever its state      *)
(* changes. The term Message is the set of all possible messages           *)
(* that can occur.                                                         *)
(***************************************************************************)

Message == [action : {"sync"}, data : State] \cup
           [action : {"add"}, data : Song, sender : Client] \cup
           [action : {"seek", "skip"}, data: Playhead, sender : Client]

(***************************************************************************)
(* The TypeOK formula states that inbox must be a function from nodes to   *)   
(* sequences of messages and state must be a function from nodes           *)
(* to states. We can ask TLC to check that TypeOK is an invariant of       *)
(* every behaviour, meaning it will find circumstances where inbox and     *)
(* state end up looking wonky. It's also useful to have as a high level    *)
(* type definition for these variables.                                    *)
(***************************************************************************)

TypeOK == /\ inbox \in [Node -> Seq(Message)]
          /\ state \in [Node -> State]

-----------------------------------------------------------------------------
(***************************************************************************)
(* Message Constructors                                                    *)
(*                                                                         *)
(* These operators are just for convenience when creating messages in      *)
(* actions below.                                                          *)
(***************************************************************************)

SyncMsg ==
  [action |-> "sync", data |-> state'[Server]]

AddMsg(client, song) ==
  [action |-> "add", data |-> song, sender |-> client]

SeekMsg(client, playhead) ==
  [action |-> "seek", data |-> playhead, sender |-> client]

SkipMsg(client, playhead) ==
  [action |-> "skip", data |-> playhead, sender |-> client]

-----------------------------------------------------------------------------
(***************************************************************************)
(* Client Actions                                                          *)
(***************************************************************************)

SendAdd(self, song) ==
  LET
    msg == AddMsg(self, song)
  IN
    /\ inbox' = [inbox EXCEPT ![Server] = Append(inbox[Server], msg)]
    /\ UNCHANGED state

RecvSync(self) ==
  /\ inbox[self] /= <<>>
  /\ LET
       msg == Head(inbox[self])
       tail == Tail(inbox[self])
     IN
       /\ msg.action = "sync"
       /\ inbox' = [inbox EXCEPT ![self] = tail]
       /\ state' = [state EXCEPT ![self] = msg.data]

SendSeek(self) ==
  LET
    playhead == state[self].playhead
    msg == SeekMsg(self, [playhead EXCEPT !.t = playhead.t + 1])
  IN
    /\ playhead /= Stopped
    /\ inbox' = [inbox EXCEPT ![Server] = Append(inbox[Server], msg)]
    /\ UNCHANGED state

SendSkip(self) ==
  LET
    playhead == state[self].playhead
    msg == SkipMsg(self, playhead)
  IN
    /\ playhead /= Stopped
    /\ inbox' = [inbox EXCEPT ![Server] = Append(inbox[Server], msg)]
    /\ UNCHANGED state

-----------------------------------------------------------------------------
(***************************************************************************)
(* Server Actions                                                          *)
(***************************************************************************)

BroadcastSync ==
  /\ inbox' = [n \in Node |-> IF n = Server
                                 THEN Tail(inbox[n])
                                 ELSE Append(inbox[n], SyncMsg)] 

RecvAdd ==
  /\ inbox[Server] /= <<>>
  /\ LET
       server == state[Server]
       msg == Head(inbox[Server])
     IN
       /\ msg.action = "add"
       /\ LET
            newPlaylist == Append(server.playlist, msg.data)
            newPlayhead == IF server.playhead = Stopped
                              THEN [i |-> Len(server.playlist), t |-> 0]
                              ELSE server.playhead
          IN
            /\ state' = [state EXCEPT ![Server] = [playlist |-> newPlaylist,
                                                   playhead |-> newPlayhead]]
            /\ BroadcastSync

RecvSeek ==
  /\ inbox[Server] /= <<>>
  /\ LET
       server == state[Server]
       msg == Head(inbox[Server])
     IN
       /\ msg.action = "seek"
       /\ state' = [state EXCEPT ![Server].playhead.t = msg.data.t]
       /\ BroadcastSync

RecvSkip ==
  /\ inbox[Server] /= <<>>
  /\ LET
       server == state[Server]
       msg == Head(inbox[Server])
     IN
       /\ msg.action = "skip"
       /\ LET
            newIndex == server.playhead.i + 1
            newPlayhead == IF newIndex < Len(server.playlist)
                              THEN [i |-> newIndex, t |-> 0]
                              ELSE Stopped
          IN
            /\ state' = [state EXCEPT ![Server].playhead = newPlayhead]
            /\ BroadcastSync

-----------------------------------------------------------------------------
(***************************************************************************)
(* Randomly lose a message from an inbox                                   *)
(***************************************************************************)

Remove(i, seq) ==
  [j \in 1..(Len(seq) - 1) |-> IF j < i THEN seq[j] ELSE seq[j + 1]] 

LoseMsg ==
  \E n \in DOMAIN inbox :
    \E i \in DOMAIN inbox[n] :
      /\ inbox' = [inbox EXCEPT ![n] = Remove(i, inbox[n])]
      /\ UNCHANGED state

-----------------------------------------------------------------------------
(***************************************************************************)
(* Spec                                                                    *)
(***************************************************************************)

Init ==
  /\ inbox = [n \in Node |-> <<>>]
  /\ state = [n \in Node |-> InitState]

Next ==
  \/ \E self \in Client, song \in Song : SendAdd(self, song)
  \/ \E self \in Client : RecvSync(self)
  \/ \E self \in Client : SendSeek(self)
  \/ \E self \in Client : SendSkip(self)
  \/ RecvAdd
  \/ RecvSeek
  \/ RecvSkip
  \/ LoseMsg

Spec ==
  Init /\ [][Next]_vars

-----------------------------------------------------------------------------

THEOREM Spec => []TypeOK

=============================================================================