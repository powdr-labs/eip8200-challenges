import Challenge.Sha256.Reference
import Challenge.Sha256.Scorer
import YulParser.Compile
set_option warningAsError true
/-!
# `sha256challenge` — the Tier-1 scorer

```sh
lake exe sha256challenge                          # score the reference Yul
lake exe sha256challenge --yul=path/to/impl.yul   # score a Yul submission
lake exe sha256challenge --hex=path/to/impl.hex   # score raw bytecode
lake exe sha256challenge --csv                    # machine-readable rows
```

Exit code 0 iff every vector returned exactly `Crypto.Sha256.hash calldata`
in both the clean and the dirty frame. See `Challenge/Sha256/Scorer.lean` for
what is run, and `README.md` for what passing does and does not mean.
-/

open EvmSemantics
open Challenge.Sha256 (referenceBytecode referenceSourcePath)
open Challenge.Sha256.Scorer

private def hexToBytes? (text : String) : Option ByteArray :=
  let text := (if text.startsWith "0x" then text.drop 2 else text).trimAscii.copy
  let text := text.replace "\n" "" |>.replace " " ""
  if text.length % 2 != 0 then none
  else if !text.all fun c =>
      ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F') then none
  else some (Hex.hexToBytes text)

private def pad (text : String) (width : Nat) : String :=
  text ++ String.ofList (List.replicate (width - text.length) ' ')

private def usage : String :=
  "usage: sha256challenge [--yul=FILE | --hex=FILE] [--csv]\n" ++
  s!"  default: {referenceSourcePath}"

def main (args : List String) : IO UInt32 := do
  if args = ["--print-reference-hex"] then
    IO.println (Hex.bytesToHex referenceBytecode)
    return 0
  let flag (name : String) : Option String :=
    args.findSome? fun arg =>
      if arg.startsWith s!"--{name}=" then some (arg.drop (name.length + 3)).copy else none
  let csv := args.contains "--csv"
  if args.contains "--help" then
    IO.println usage
    return 0
  -- A scoring run that disagrees with FIPS 180-4 is not a scoring run.
  for (input, expected) in oracleChecks do
    if Hex.bytesToHex (Challenge.Sha256.spec input) != expected then
      IO.eprintln "sha256challenge: the canonical spec disagrees with FIPS 180-4"
      return 3
  let (name, code) ←
    match flag "hex", flag "yul" with
    | some _, some _ => do IO.eprintln usage; return 64
    | some path, none => do
        match hexToBytes? (← IO.FS.readFile path) with
        | none => do IO.eprintln s!"{path}: not a hex bytecode file"; return 64
        | some code => pure (path, code)
    | none, yulPath => do
        let path := yulPath.getD referenceSourcePath
        let source ← IO.FS.readFile path
        match YulParser.compileSource source with
        | none => do
            IO.eprintln s!"{path}: rejected by the verified compiler"
            return 2
        | some code => pure (path, code)
  if csv then
    IO.println "vector,bytes,frame,status,gas"
  else
    IO.println s!"== {name} =="
    IO.println s!"bytecode: {code.size} bytes"
    IO.println ""
    IO.println s!"{pad "vector" 26}{pad "bytes" 7}{pad "clean gas" 12}{pad "dirty gas" 12}status"
  let mut failures := 0
  let mut totalGas := 0
  let mut totalBytes := 0
  for v in vectors do
    let (clean, dirty, status) := verdict code v
    if !status.startsWith "ok" then failures := failures + 1
    match clean with
    | .ok gas => do totalGas := totalGas + gas; totalBytes := totalBytes + v.input.size
    | _ => pure ()
    let gasText (o : Outcome) : String :=
      match o.gas? with | some g => toString g | none => "-"
    if csv then
      IO.println s!"{v.label},{v.input.size},clean,{status},{gasText clean}"
      IO.println s!"{v.label},{v.input.size},dirty,{status},{gasText dirty}"
    else
      IO.println s!"{pad v.label 26}{pad (toString v.input.size) 7}\
        {pad (gasText clean) 12}{pad (gasText dirty) 12}{status}"
  if !csv then
    IO.println ""
    IO.println s!"total gas over all vectors: {totalGas} ({totalBytes} input bytes)"
    if failures == 0 then
      IO.println "Tier 1: PASS — every vector matches EvmSemantics.Crypto.Sha256.hash"
    else
      IO.println s!"Tier 1: FAIL — {failures} vector(s) mismatched"
  return (if failures == 0 then 0 else 1)
