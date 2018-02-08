-------------------------------- MODULE HKFM --------------------------------
EXTENDS Integers, Sequences
CONSTANTS Client, Song
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
            [action : {"add"}, data : Song, sender : Client] \cup
            [action : {"seek", "skip"}, data: Playhead, sender : Client]

TypeOK   == /\ inbox \in [Node -> Seq(Message)]
            /\ state \in [Node -> State]

-----------------------------------------------------------------------------
(***************************************************************************)
(* Message Constructors                                                    *)
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
    msg == SeekMsg(self, [playhead EXCEPT !.t = playhead.t + 1])
  IN
    /\ playhead.i # -1
    /\ inbox' = [inbox EXCEPT ![Server] = Append(inbox[Server], msg)]
    /\ UNCHANGED state

SendSkip(self) ==
  LET
    playhead == state[self].playhead
    msg == SkipMsg(self, playhead)
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
  /\ LET
       server == state[Server]
       msg == Head(inbox[Server])
     IN
       /\ msg.action = "add"
       /\ LET
            newPlaylist == Append(server.playlist, msg.data)
            newPlayhead == IF server.playhead.i = -1
                              THEN [i |-> Len(server.playlist), t |-> 0]
                              ELSE server.playhead
          IN
            /\ state' = [state EXCEPT ![Server] = [playlist |-> newPlaylist,
                                                   playhead |-> newPlayhead]]
            /\ BroadcastSync

RecvSeek ==
  /\ inbox[Server] # <<>>
  /\ LET
       server == state[Server]
       msg == Head(inbox[Server])
     IN
       /\ msg.action = "seek"
       /\ msg.data.i = server.playhead.i
       /\ msg.data.t > server.playhead.t
       /\ state' = [state EXCEPT ![Server].playhead.t = msg.data.t]
       /\ BroadcastSync

RecvSkip ==
  /\ inbox[Server] # <<>>
  /\ LET
       server == state[Server]
       msg == Head(inbox[Server])
     IN
       /\ msg.action = "skip"
       /\ msg.data.i = server.playhead.i
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
(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

PlayheadOK ==
  LET
    server == state[Server].playhead
  IN
    \/ server = Stopped
    \/ \A c \in Client :
        LET
          client == state[c].playhead
        IN
          \/ client.i < server.i
          \/ /\ client.i = server.i
             /\ client.t =< server.t

SeekAdvances ==
  \/ state[Server].playhead.i /= state'[Server].playhead.i
  \/ state[Server].playhead.t =< state'[Server].playhead.t

Synced ==
  \A c \in Client : state[c] = state[Server]

-----------------------------------------------------------------------------

THEOREM Spec => []TypeOK
THEOREM Spec => []PlayheadOK
THEOREM Spec => []<>Synced
THEOREM Spec => [][SeekAdvances]_vars

=============================================================================