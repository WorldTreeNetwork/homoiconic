# logged-processes

What is built: several processes that talk over channels (`openspec/specs/channels/spec.md`), driven by a log of identified events and kept under a root. The definitions are in `kernel/Reflect/Node.lean`, the proofs in `kernel/Reflect/NodeProof.lean`, and the exact statements in `kernel/NodeContract.lean`.

## Purpose

State what an op does to a node and what is proved about the node a log leads to. An op that is read is named by its hash. This spec does not say how events are chosen, or anything about two nodes.

## Requirements

### Requirement: An op is an event with an identifier

An op SHALL be an identifier, which is data, and an event of `openspec/specs/channels/spec.md`. A node SHALL be a configuration of processes together with the identifiers of the ops it has acted on. Applying an op SHALL do one of two things (`Reflect.Apply`). When the node has acted on the op's identifier, the node SHALL be unchanged. Otherwise the event SHALL happen as `Reflect.Step` says and the identifier SHALL be recorded. An op whose event cannot happen, or whose evaluation never finishes, SHALL have no next node. The node of a program and a log SHALL be what applying the log, op by op, leads to from the program as the first process (`Reflect.Ran`).

#### Scenario: A log of six ops

- GIVEN `examples/ping.hom` and `examples/ping.log`
- WHEN the node applies the log from the start
- THEN it acts on six ops, process 0 finishes with 42 and process 1 with `[41]`

### Requirement: A node is a function of its program and its log

For every operation table, a program and a log SHALL lead to at most one node (`node_deterministic`), and the node after a log SHALL be the node after any first part of it, carried on through the rest (`node_prefix`).

#### Scenario: Replay

- GIVEN `Ran sourceP p ops a` and `Ran sourceP p ops b`
- WHEN `kernel/NodeContract.lean` is checked
- THEN `a = b`

### Requirement: An op already in the log changes nothing

For every operation table, applying an op that is in the log a node was reached by SHALL leave the node as it is and SHALL lead nowhere else (`node_again`). A log with an op of its first part delivered again later SHALL lead to the nodes the log without that delivery leads to (`node_redeliver`). A node reached by a first part of a log, applying the whole log, SHALL reach exactly the nodes the whole log reaches from the start (`node_restart`).

#### Scenario: Delivered again

- GIVEN `examples/ping.hom` and `examples/ping-again.log`, ten deliveries of the six ops
- WHEN the node applies the log
- THEN it acts on six ops and has the root `examples/ping.log` gives

### Requirement: A node's processes follow the schedule of first deliveries

For every operation table, the configuration of a node SHALL be one the program reaches, as `Reflect.Network`, through the events of the log's first deliveries in their order (`node_network`).

#### Scenario: The channel theorems apply

- GIVEN `Ran sourceP p ops n`
- WHEN `kernel/NodeContract.lean` is checked
- THEN `Network sourceP p ((firstOps [] ops).map (·.event)) n.cfg` holds

### Requirement: The machine applies a log as the program does

For every operation table and every program, the node the machine reaches by a log SHALL be the compiled form of the node direct evaluation reaches (`node_machine`, `node_machine_exact`). The executable `nodeRun` SHALL apply ops in order, pass over an op whose identifier was acted on, and stop at the first op whose event cannot happen or does not halt within the budget. The ops it reports as applied SHALL be a log of the program by direct evaluation, and the node it reports SHALL be the compiled form of where that log leads, however it stopped (`node_true`).

#### Scenario: The report is true

- GIVEN `beginRun budget p = some c₀` and any ops
- WHEN `kernel/NodeContract.lean` is checked
- THEN there is a node `n` with `Ran sourceP p (nodeRun budget ⟨c₀, []⟩ ops).1 n` whose compiled form is the node reported

### Requirement: An event is a plan of machine runs

`Reflect.plan` SHALL give, for a configuration and an event, the machine runs the event needs in order and the configuration once they have ended, or nothing when the event cannot happen. For every way of evaluating, an event SHALL happen exactly when the plan's runs end somewhere and the plan gives the next configuration from there (`plan_step`, `step_plan`).

#### Scenario: Both ways

- GIVEN any configuration, event and way of evaluating
- WHEN `kernel/NodeContract.lean` is checked
- THEN `plan_step` and `step_plan` hold with the signatures stated there

### Requirement: A node is kept under a root

`Surface.Keep` SHALL apply a log of ops against a store it is handed piece by piece: from a program's source (`nodeStart`) or from the root of a kept node (`nodeFrom`). It SHALL decide whether an event can happen, which runs it needs and the configuration after it by `Reflect.plan`, and SHALL run each job on the lazy machine. When the log is applied, or an op cannot happen, it SHALL save the node as the piece `[seen, names, processes]`, each process `[held, status]`, with `status` being `[0, function, payload]`, `[1, data]`, `[2, i]` or `[3]`, and SHALL report each process, how many ops were given and acted on, an op that could not happen, and the root. After an op that cannot happen it SHALL apply no further op. A root that does not name exactly such a piece SHALL be refused as text; a function's environment SHALL NOT be walked. A run that does not end within its budget SHALL save nothing. The session SHALL be compared with `nodeRun` by `kernel/NodeCheck.lean`. What the session computes is tested, not proved. It is proved that the session holds and saves only references saving made (`advance_kept`, `nodeStart_kept`, `nodeFrom_kept`), and that two pieces that stand for one node are saved under one root (`node_same_root`, `node_restart_same_root`); that the session's piece stands for the node `Reflect.Ran` gives is a hypothesis of `node_restart_root` (`openspec/specs/wire-bytes/spec.md`, "A VM's and a node's session save only references saving made").

#### Scenario: The session and nodeRun agree

- GIVEN `examples/ping.hom`, `examples/race.hom` and `examples/guess.hom`, each with the schedule the chooser picks, numbered as a log
- WHEN `kernel/NodeCheck.lean` runs
- THEN every line starts with `ok`: the roots agree at every prefix, a node kept at any prefix and given the whole log reaches the whole log's root, and nine malformed pieces are refused

### Requirement: The node theorems depend on the logic only

`kernel/NodeContract.lean` SHALL state each theorem for every operation table or every way of evaluating, SHALL NOT import a table, and SHALL print each theorem's axioms. The axioms SHALL be among `propext`, `Classical.choice` and `Quot.sound`.

#### Scenario: Axioms

- GIVEN the built kernel
- WHEN `lake env lean NodeContract.lean` runs
- THEN it exits 0 and prints no axiom outside those three

### Requirement: An op that is read is named by its hash

An op of a log that is read SHALL be written as a mark and an event, and its identifier SHALL be the name `Surface.Keep.entryName` gives to that pair as written (`Reflect.Op.seal`). The kernel SHALL compute the name. For every function `key` that gives different names to different data and every way of reading an event from data, two sealed ops with one identifier SHALL be one op (`sealed_op_same`), and every op of a log whose ops are all sealed SHALL be among the log's first deliveries (`sealed_op_first`). An op that cannot happen SHALL be reported by its place in the log, counted from 0, and its event.

#### Scenario: The statement

- GIVEN `Function.Injective key`, two ops sealed under `key` and one `read`, and equal identifiers
- WHEN `kernel/NodeContract.lean` is checked
- THEN the ops are equal

#### Scenario: The session and nodeRun agree on sealed ops

- GIVEN the logs of `kernel/NodeCheck.lean`, each op sealed for `nodeRun` as the session seals it
- WHEN `kernel/NodeCheck.lean` runs
- THEN every line starts with `ok`
