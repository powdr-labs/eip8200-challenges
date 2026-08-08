import Challenge.Modexp.Reference
import Challenge.Modexp.Scorer
import YulParser.Compile
set_option warningAsError true

open EvmSemantics
open Challenge.Modexp
open Challenge.Modexp.Scorer

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
  "usage: modexpchallenge [--yul=FILE | --hex=FILE] [--csv]\n" ++
  s!"  default: {referenceSourcePath}"

def main (args : List String) : IO UInt32 := do
  if args = ["--print-reference-hex"] then
    IO.println (Hex.bytesToHex referenceBytecode)
    return 0
  let hexPath := args.findSome? fun arg =>
    if arg.startsWith "--hex=" then some (arg.drop 6).copy else none
  let yulPath := args.findSome? fun arg =>
    if arg.startsWith "--yul=" then some (arg.drop 6).copy else none
  let csv := args.contains "--csv"
  if args.contains "--help" then
    IO.println usage
    return 0
  let (name, code) : System.FilePath × ByteArray ← match hexPath, yulPath with
    | some _, some _ => do IO.eprintln usage; return 64
    | some path, none =>
        match hexToBytes? (← IO.FS.readFile path) with
        | some bytes => pure (path, bytes)
        | none => do IO.eprintln s!"{path}: invalid hex"; return 64
    | none, maybePath =>
        let path := maybePath.getD referenceSourcePath
        match YulParser.compileSource (← IO.FS.readFile path) with
        | some bytes => pure (System.FilePath.mk path, bytes)
        | none => do IO.eprintln s!"{path}: compiler rejected source"; return 2

  if csv then
    IO.println "vector,bytes,status,gas,precompile"
  else
    IO.println s!"== {name} ==\nbytecode: {code.size} bytes\n"
    IO.println s!"{pad "vector" 30}{pad "bytes" 7}{pad "gas" 12}\
      {pad "precompile" 12}status"
  let mut failures := 0
  let mut totalGas := 0
  let mut totalPrecompile := 0
  for vector in vectors do
    let outcome := score code vector.input
    let expectedGas := precompileGas vector.input
    let gasText := match outcome.gas? with | some gas => toString gas | none => "-"
    let status := match outcome with
      | .ok _ => "ok"
      | .wrongResult _ _ _ => "wrong result"
      | .badHalt halt _ => s!"halted {halt}"
      | .outOfFuel => "out of fuel"
    match outcome with
    | .ok gas => totalGas := totalGas + gas
    | .wrongResult _ _ _ =>
        failures := failures + 1
    | .badHalt _ _ =>
        failures := failures + 1
    | .outOfFuel =>
        failures := failures + 1
    totalPrecompile := totalPrecompile + expectedGas
    if csv then
      IO.println s!"{vector.label},{vector.input.size},{status},{gasText},{expectedGas}"
    else
      IO.println s!"{pad vector.label 30}{pad (toString vector.input.size) 7}\
        {pad gasText 12}{pad (toString expectedGas) 12}{status}"
      match outcome with
      | .wrongResult got expected _ =>
          IO.println s!"  got {got}\n  expected {expected}"
      | _ => pure ()
  if !csv then
    IO.println ""
    IO.println s!"total gas over all vectors: {totalGas}"
    IO.println s!"Osaka precompile total: {totalPrecompile}"
    IO.println (if failures = 0 then "Tier 1: PASS" else
      s!"Tier 1: FAIL — {failures} vector(s)")
  return if failures = 0 then 0 else 1
