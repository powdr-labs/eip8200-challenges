import Challenge.Ripemd160.Reference
import Challenge.Ripemd160.Scorer
import YulParser.Compile
set_option warningAsError true

open EvmSemantics
open Challenge.Ripemd160 (referenceBytecode referenceSourcePath)
open Challenge.Ripemd160.Scorer

private def hexToBytes? (text : String) : Option ByteArray :=
  let text := (if text.startsWith "0x" then text.drop 2 else text).trimAscii.copy
  let text := text.replace "\n" "" |>.replace " " ""
  if text.length % 2 != 0 then none
  else if !text.all fun c =>
      ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F') then none
  else some (Hex.hexToBytes text)

private def pad (text : String) (width : Nat) : String :=
  text ++ String.ofList (List.replicate (width - text.length) ' ')

def main (args : List String) : IO UInt32 := do
  if args = ["--print-reference-hex"] then
    IO.println (Hex.bytesToHex referenceBytecode)
    return 0
  let flag (name : String) : Option String :=
    args.findSome? fun arg =>
      if arg.startsWith s!"--{name}=" then some (arg.drop (name.length + 3)).copy else none
  let csv := args.contains "--csv"
  for (input, expected) in oracleChecks do
    if Hex.bytesToHex (Challenge.Ripemd160.spec input) != expected then
      IO.eprintln "ripemd160challenge: pinned semantics disagrees with published vectors"
      return 3
  let (name, code) ←
    match flag "hex", flag "yul" with
    | some _, some _ => do IO.eprintln "choose one of --hex or --yul"; return 64
    | some path, none => do
        match hexToBytes? (← IO.FS.readFile path) with
        | none => do IO.eprintln s!"{path}: invalid hex"; return 64
        | some code => pure (path, code)
    | none, yulPath => do
        let path := yulPath.getD referenceSourcePath
        match YulParser.compileSourceWithBackend (← IO.FS.readFile path) [] .classic with
        | none => do IO.eprintln s!"{path}: compiler rejected source"; return 2
        | some code => pure (path, code)
  if csv then IO.println "vector,bytes,frame,status,gas"
  else
    IO.println s!"== {name} =="
    IO.println s!"bytecode: {code.size} bytes\n"
    IO.println s!"{pad "vector" 18}{pad "bytes" 7}{pad "clean gas" 12}{pad "dirty gas" 12}status"
  let mut failures := 0
  let mut totalGas := 0
  for v in vectors do
    let (clean, dirty, status) := verdict code v
    if !status.startsWith "ok" then failures := failures + 1
    match clean with | .ok gas => totalGas := totalGas + gas | _ => pure ()
    let gasText (o : Outcome) : String :=
      match o.gas? with | some g => toString g | none => "-"
    if csv then
      IO.println s!"{v.label},{v.input.size},clean,{status},{gasText clean}"
      IO.println s!"{v.label},{v.input.size},dirty,{status},{gasText dirty}"
    else
      IO.println s!"{pad v.label 18}{pad (toString v.input.size) 7}{pad (gasText clean) 12}{pad (gasText dirty) 12}{status}"
  if !csv then
    IO.println s!"\ntotal gas over all vectors: {totalGas}"
    IO.println (if failures == 0 then "Tier 1: PASS" else s!"Tier 1: FAIL — {failures} vector(s)")
  return if failures == 0 then 0 else 1
