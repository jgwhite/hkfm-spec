-------------------------------- MODULE HKFM --------------------------------
EXTENDS Integers, Sequences
CONSTANT Client, Song
VARIABLES inbox, state
-----------------------------------------------------------------------------
(***************************************************************************)
(* Definitions                                                             *)
(***************************************************************************)

vars     == <<inbox, state>>

Server   == CHOOSE x : x \notin Client
Node     == Client \cup {Server}

Idx       == Nat \cup {-1}
Playlist  == Seq(Song)
Playhead  == [i : Idx, t : Nat]
Stopped   == [i |-> -1, t |-> 0]
State     == [playlist : Playlist, playhead : Playhead]
InitState == [playlist |-> <<>>, playhead |-> Stopped]

Message  == [action : {"sync"}, data : State] \cup
            [action : {"add"}, data : Song] \cup
            [action : {"seek", "skip"}, data: Playhead] 

TypeOK   == /\ inbox \in [Node -> Seq(Message)]
            /\ state \in [Node -> State]

-----------------------------------------------------------------------------
(***************************************************************************)
(* Message Constructors                                                    *)
(***************************************************************************)

SyncMsg ==
  [action |-> "sync", data |-> state'[Server]]

AddMsg(song) ==
  [action |-> "add", data |-> song]

SeekMsg(playhead) ==
  [action |-> "seek", data |-> [playhead EXCEPT !.t = playhead.t + 1]]

SkipMsg(playhead) ==
  [action |-> "skip", data |-> playhead]

-----------------------------------------------------------------------------
(***************************************************************************)
(* Client Actions                                                          *)
(***************************************************************************)

SendAdd(song) ==
  LET
    msg == AddMsg(song)
  IN
    /\ inbox' = [inbox EXCEPT ![Server] = Append(inbox[Server], msg)]
    /\ UNCHANGED state

RecvSync(self) ==
  /\ inbox[self] # <<>>
  /\ Head(inbox[self]).action = "sync"
  /\ LET
       newState == Head(inbox[self]).data
     IN
       /\ inbox' = [inbox EXCEPT ![self] = Tail(inbox[self])]
       /\ state' = [state EXCEPT ![self] = newState]

SendSeek(self) ==
  LET
    playhead == state[self].playhead
    msg == SeekMsg(playhead)
  IN
    /\ playhead.i # -1
    /\ inbox' = [inbox EXCEPT ![Server] = Append(inbox[Server], msg)]
    /\ UNCHANGED state

SendSkip(self) ==
  LET
    playhead == state[self].playhead
    msg == SkipMsg(playhead)
  IN
    /\ playhead.i # -1
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
  /\ inbox[Server] # <<>>
  /\ Head(inbox[Server]).action = "add"
  /\ LET
       song        == Head(inbox[Server]).data
       playlist    == state[Server].playlist
       playhead    == state[Server].playhead
       newPlaylist == Append(playlist, song)
       newPlayhead == IF playhead.i = -1
                         THEN [i |-> Len(playlist), t |-> 0]
                         ELSE playhead
     IN
       /\ state' = [state EXCEPT ![Server] = [playlist |-> newPlaylist,
                                              playhead |-> newPlayhead]]
       /\ BroadcastSync

RecvSeek ==
  /\ inbox[Server] # <<>>
  /\ Head(inbox[Server]).action = "seek"
  /\ LET
       data     == Head(inbox[Server]).data
       playhead == state[Server].playhead
     IN
       /\ state' = [state EXCEPT ![Server].playhead.t = data.t]
       /\ BroadcastSync

RecvSkip ==
  /\ inbox[Server] # <<>>
  /\ Head(inbox[Server]).action = "skip"
  /\ LET
       data        == Head(inbox[Server]).data
       playlist    == state[Server].playlist
       playhead    == state[Server].playhead
       newIndex    == playhead.i + 1
       newPlayhead == IF newIndex < Len(playlist)
                         THEN [i |-> newIndex, t |-> 0]
                         ELSE Stopped
     IN
       /\ state' = [state EXCEPT ![Server].playhead = newPlayhead]
       /\ BroadcastSync

-----------------------------------------------------------------------------
(***************************************************************************)
(* Spec                                                                    *)
(***************************************************************************)

Init ==
  /\ inbox = [n \in Node |-> <<>>]
  /\ state = [n \in Node |-> InitState]

Next ==
  \/ \E song \in Song : SendAdd(song)
  \/ \E self \in Client : RecvSync(self)
  \/ \E self \in Client : SendSeek(self)
  \/ \E self \in Client : SendSkip(self)
  \/ RecvAdd
  \/ RecvSeek
  \/ RecvSkip

Spec ==
  Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

THEOREM Spec => []TypeOK

=============================================================================