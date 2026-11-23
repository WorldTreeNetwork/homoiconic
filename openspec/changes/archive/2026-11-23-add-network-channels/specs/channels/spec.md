# channels delta: a channel whose other end is another machine

## ADDED Requirements

### Requirement: A function and a reply name cross to another machine

`kernel/Surface/Remote.lean` SHALL hold one program, `Surface.Remote.program`, whose text is `examples/remote.hom`. Its first process makes a channel `remote` and starts a peer on it, makes a reply channel, sends `[worker, reply]` on `remote`, and receives on `reply`; `worker` is a quoted function that sends 42 on the name it is given. The offer SHALL be the message of the first send that run makes, found by running the events the executable scheduler picks until it picks a send meeting a receive, and taking the message of that send (`offerOf`), written in the byte form (`Wire.write`; `offerBytes`): the data form of the quoted function and the reply name value. Taking an offer (`takeBytes`) SHALL read the byte form, SHALL accept only an array of a term's data form and a name value, SHALL turn the data back into its term, start it as a process applied to that name value (`beginRun`, budget 100000), and give the byte form of the message when that process is waiting to send on that same name; anything else SHALL give empty bytes. Taking an offer runs the function only to its first send; it is not run by the scheduler, and it is not a process of the other machine's run.

#### Scenario: The reply comes back

- GIVEN `offerBytes`
- WHEN `takeBytes` runs on it
- THEN the bytes read back as 42 (`Surface.Remote.same`, `kernel/RemoteCheck.lean`)

### Requirement: The schedule replays on one machine

`Surface.Remote.logText` SHALL be the schedule the executable scheduler takes for the program on one machine (`autoRun`, budget 100000, at most 40 events), written as a schedule file writes it. `Surface.Remote.same` SHALL be true only when that run stops with neither a refused nor an unfinished event (`.ran`, which also covers stopping at the limit), its first process has finished with 42, an offer exists, and taking the offer gives the byte form of 42. Given back as a schedule, that log runs the same events, as for any program (`network_deterministic`, and the interpreter on data as well, `network_reflective`). The log is not recorded from the guests: no order of delivery between machines is captured, and no received schedule is replayed (`homoiconic-q59.51`). What `same` checks is tested, not proved.

#### Scenario: The remote program replays to 42

- GIVEN `kernel/RemoteCheck.lean`
- WHEN it is run with `lake env lean`
- THEN it prints `ok   a remote closure replays to 42`

#### Scenario: The log is a schedule

- GIVEN `examples/remote.hom`
- WHEN it runs with no schedule through `reflect_channels`, and again with the schedule `Surface.Remote.logText`
- THEN both print the schedule `[[0, 0, 0], [1, 0], [0, 0, 1], [2, 0, 1], [1, 1], [2, 2, 0]]` and the first process finished with 42 (checked by hand with `Surface.channelsText` on 2026-11-23)

### Requirement: An unforgeable name across machines is a hypothesis

Inside one machine the theorems of this spec SHALL be the whole claim about names. Across machines nothing SHALL be claimed proved: on the wire a name value is a number in the byte form, the machine that takes an offer uses the number it is sent as the name, and that another machine cannot forge a name, or reach a name it was not sent, is a hypothesis about the host, the network and the peer, stated and not proved.

#### Scenario: No theorem for two machines

- GIVEN `kernel/ChannelContract.lean`
- WHEN it is read
- THEN no statement in it is about a second machine, an offer or the wire
