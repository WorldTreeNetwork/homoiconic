# state-store

## MODIFIED Requirements

### Requirement: What a reference means is assumed
<!-- base: dedffcce68cf2d46b94f74c0a9f2dc01c2a23390 openspec/specs/state-store/spec.md -->

That a reference names one piece and never another SHALL be a stated hypothesis: a store is a function, a larger store holds the same piece under every reference the smaller one holds, and two stores are compared only when they agree wherever both hold a piece. No theorem of this spec SHALL depend on how references are made or checked. References are made by hashing a piece's bytes and checked by the session that runs a turn (`openspec/specs/wire-bytes/spec.md`); both are Lean definitions, tested and not proved.

#### Scenario: The hypothesis is visible

- GIVEN `kernel/StoreContract.lean`
- WHEN a theorem relates two stores
- THEN it states `σ.le τ` or `σ.Compatible τ`
