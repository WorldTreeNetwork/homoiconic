# state-store

## ADDED Requirements

### Requirement: A turn runs against a store it is handed piece by piece

The kernel SHALL provide a session that runs one turn of a program on the lazy machine: the first turn from a program's source, or a later turn from the root of a waiting program and an answer. When the turn needs a piece the session does not hold, the session SHALL stop and name that piece, and SHALL continue from where it stopped when the piece is supplied. It SHALL refuse a supplied piece whose hash is not the name it asked for. When the turn ends in a request it SHALL save the waiting program and report the request's payload, the root, and the pieces to be stored, leaving out any piece it was supplied. When the turn ends in a result it SHALL report the result. The session is tested, not proved.

#### Scenario: Three turns are one run

- GIVEN a program that asks twice
- WHEN it is started, then answered from its root in a new session, then answered again from the new root in a third
- THEN the requests and the result are those of one run against both answers

#### Scenario: A turn reads only what it looks at

- GIVEN a waiting program that holds a long list its next turn does not use
- WHEN that turn runs
- THEN it is supplied fewer pieces than the list has, and hands back none of the list's pieces
