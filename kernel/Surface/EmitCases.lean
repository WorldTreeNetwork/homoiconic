import Surface.Expect

/-!
Writes `Surface.prints` as Zig source on stdout, so the host check passes exactly
the programs `Expect.lean` lists and Zig holds only bytes. Run by `host/check.sh`:
`lake env lean --run Surface/EmitCases.lean`.
-/
open Surface

def zigString (s : String) : String :=
  "\"" ++ (s.foldl (fun acc c =>
    acc ++ (if c == '\n' then "\\n" else if c == '"' then "\\\"" else if c == '\\' then "\\\\"
            else c.toString)) "") ++ "\""

def main : IO Unit := do
  IO.println "// Generated from kernel/Surface/Expect.lean by Surface/EmitCases.lean."
  IO.println "pub const Print = struct { program: []const u8, budget: u64, expected: []const u8 };"
  IO.println "pub const prints = [_]Print{"
  for (text, budget, out) in prints do
    IO.println s!"    .\{ .program = {zigString text}, .budget = {budget}, .expected = {zigString out} },"
  IO.println "};"
