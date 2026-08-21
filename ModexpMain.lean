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
  "usage: modexpchallenge [--yul=FILE | --hex=FILE] [--csv] " ++
  "[--fuzz=COUNT] [--seed=N]\n" ++
  s!"  default: {referenceSourcePath}"

/-! The fuzz stream is intentionally small and deterministic.  It exercises
the same compiled bytecode and `spec` oracle as the public scorer without
making a random-number generator part of the trusted proof surface. -/

private def nextSeed (seed : Nat) : Nat :=
  (6364136223846793005 * seed + 1442695040888963407) % (2 ^ 64)

private def draw (seed bound : Nat) : Nat × Nat :=
  let seed' := nextSeed seed
  (seed' % bound, seed')

private def fuzzInput (index seed : Nat) : ByteArray × Nat :=
  let (bsizeRaw, seed) := draw seed 9
  let (esizeRaw, seed) := draw seed 5
  let (msizeRaw, seed) := draw seed 33
  let (baseRaw, seed) := draw seed (2 ^ 64)
  let (exponentRaw, seed) := draw seed (2 ^ 16)
  let (modulusRaw, seed) := draw seed (2 ^ 64)
  let (truncateMode, seed) := draw seed 5
  let (tailKeep, seed) := draw seed 128
  -- Periodically force the limb path.  Keeping the exponent to one byte makes
  -- these cases useful without turning a local fuzz run into a benchmark.
  let big := index % 32 = 31
  let bsize := if big then bsizeRaw % 3 else bsizeRaw
  let esize := if big then esizeRaw % 2 else esizeRaw
  let msize := if big then 33 else msizeRaw
  let modulus := if index % 11 = 0 then 0 else modulusRaw
  let full := makeInput baseRaw exponentRaw modulus bsize esize msize
  let input :=
    if truncateMode = 0 then
      full.extract 0 (tailKeep % 97)
    else if truncateMode = 1 then
      full.extract 0 (Nat.min full.size
        (96 + tailKeep % (bsize + esize + msize + 1)))
    else
      full
  (input, seed)

private def runFuzz (code : ByteArray) (count seed : Nat) : IO Nat := do
  let initialSeed := seed
  let mut seed := seed
  let mut failures := 0
  for index in [0:count] do
    let (input, seed') := fuzzInput index seed
    seed := seed'
    match score code input with
    | .ok _ => pure ()
    | .wrongResult got expected gas =>
        failures := failures + 1
        IO.eprintln s!"fuzz #{index} failed (seed {initialSeed}, gas {gas})"
        IO.eprintln s!"  calldata: {Hex.bytesToHex input}"
        IO.eprintln s!"  got:      {got}"
        IO.eprintln s!"  expected: {expected}"
    | .badHalt halt gas =>
        failures := failures + 1
        IO.eprintln s!"fuzz #{index} halted {halt} (seed {initialSeed}, gas {gas})"
        IO.eprintln s!"  calldata: {Hex.bytesToHex input}"
    | .outOfFuel =>
        failures := failures + 1
        IO.eprintln s!"fuzz #{index} ran out of fuel (seed {initialSeed})"
        IO.eprintln s!"  calldata: {Hex.bytesToHex input}"
  IO.println (if failures = 0 then
    s!"Fuzz: PASS ({count} deterministic cases, seed {initialSeed})"
  else
    s!"Fuzz: FAIL ({failures}/{count} cases, seed {initialSeed})")
  pure failures

def main (args : List String) : IO UInt32 := do
  if args = ["--print-reference-hex"] then
    IO.println (Hex.bytesToHex referenceBytecode)
    return 0
  let hexPath := args.findSome? fun arg =>
    if arg.startsWith "--hex=" then some (arg.drop 6).copy else none
  let yulPath := args.findSome? fun arg =>
    if arg.startsWith "--yul=" then some (arg.drop 6).copy else none
  let fuzzText? := args.findSome? fun arg =>
    if arg.startsWith "--fuzz=" then some (arg.drop 7).copy else none
  let seedText? := args.findSome? fun arg =>
    if arg.startsWith "--seed=" then some (arg.drop 7).copy else none
  let fuzzCount? := fuzzText?.bind String.toNat?
  let seed? := seedText?.bind String.toNat?
  let csv := args.contains "--csv"
  if args.contains "--help" then
    IO.println usage
    return 0
  if (fuzzText?.isSome && fuzzCount?.isNone) ||
      (seedText?.isSome && seed?.isNone) ||
      (seed?.isSome && fuzzCount?.isNone) then
    IO.eprintln usage
    return 64
  if csv && fuzzCount?.isSome then
    IO.eprintln "--csv and --fuzz cannot be combined"
    return 64
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
  if let some fuzzCount := fuzzCount? then
    failures := failures + (← runFuzz code fuzzCount (seed?.getD 8200))
  return if failures = 0 then 0 else 1
