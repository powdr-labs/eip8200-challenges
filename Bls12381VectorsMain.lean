import Challenge.Bls12381.Gas
import Challenge.Bls12381G1Add.Spec
import Challenge.Bls12381G1Msm.Spec
import Challenge.Bls12381G2Add.Spec
import Challenge.Bls12381G2Msm.Spec
import Challenge.Bls12381MapFpToG1.Spec
import Challenge.Bls12381MapFp2ToG2.Spec
import Challenge.Bls12381Pairing.Spec
import EvmSemantics.Data.Hex
import Lean.Data.Json

set_option warningAsError true

open EvmSemantics

private structure OfficialVector where
  name : String
  input : String
  expected : String
  gas : Nat

private instance : Lean.FromJson OfficialVector where
  fromJson? json := do
    return {
      name := ← json.getObjValAs? String "Name"
      input := ← json.getObjValAs? String "Input"
      expected := ← json.getObjValAs? String "Expected"
      gas := ← json.getObjValAs? Nat "Gas" }

private structure FailureVector where
  name : String
  input : String

private instance : Lean.FromJson FailureVector where
  fromJson? json := do
    return {
      name := ← json.getObjValAs? String "Name"
      input := ← json.getObjValAs? String "Input" }

private structure Target where
  spec : ByteArray → Option ByteArray
  operation : Challenge.Bls12381.Gas.Operation

private def target? : String → Option Target
  | "g1add" => some ⟨Challenge.Bls12381G1Add.spec, .g1Add⟩
  | "g1msm" => some ⟨Challenge.Bls12381G1Msm.spec, .g1Msm⟩
  | "g2add" => some ⟨Challenge.Bls12381G2Add.spec, .g2Add⟩
  | "g2msm" => some ⟨Challenge.Bls12381G2Msm.spec, .g2Msm⟩
  | "pairing" => some ⟨Challenge.Bls12381Pairing.spec, .pairing⟩
  | "map-fp-g1" => some ⟨Challenge.Bls12381MapFpToG1.spec, .mapFpToG1⟩
  | "map-fp2-g2" => some ⟨Challenge.Bls12381MapFp2ToG2.spec, .mapFp2ToG2⟩
  | _ => none

private def usage : String :=
  "usage: bls12381vectors TARGET FILE [--fail]\n" ++
  "TARGET: g1add | g1msm | g2add | g2msm | pairing | map-fp-g1 | map-fp2-g2"

def main (args : List String) : IO UInt32 := do
  let (targetName, path, failuresOnly) ← match args with
    | [targetName, path] => pure (targetName, path, false)
    | [targetName, path, "--fail"] => pure (targetName, path, true)
    | _ => IO.eprintln usage; return 64
  let some target := target? targetName | IO.eprintln usage; return 64
  let text ← IO.FS.readFile path
  let json ← match Lean.Json.parse text with
    | .ok value => pure value
    | .error error => IO.eprintln s!"{path}: {error}"; return 2
  if failuresOnly then
    let vectors ← match (Lean.fromJson? json : Except String (Array FailureVector)) with
      | .ok value => pure value
      | .error error => IO.eprintln s!"{path}: {error}"; return 2
    let mut failures := 0
    for vector in vectors do
      if (target.spec (Hex.hexToBytes vector.input)).isSome then
        failures := failures + 1
        IO.eprintln s!"FAIL {vector.name}: rejected vector returned a value"
    if failures = 0 then
      IO.println s!"PASS {vectors.size} official rejection vectors"
      return 0
    else
      IO.eprintln s!"FAIL {failures} mismatch(es)"
      return 1
  else
    let vectors ← match (Lean.fromJson? json : Except String (Array OfficialVector)) with
      | .ok value => pure value
      | .error error => IO.eprintln s!"{path}: {error}"; return 2
    let mut failures := 0
    for vector in vectors do
      let input := Hex.hexToBytes vector.input
      let expected := Hex.hexToBytes vector.expected
      let got := target.spec input
      let gas := Challenge.Bls12381.Gas.precompileCost target.operation input
      if got != some expected then
        failures := failures + 1
        IO.eprintln s!"FAIL {vector.name}: output mismatch"
      if gas != vector.gas then
        failures := failures + 1
        IO.eprintln s!"FAIL {vector.name}: gas {gas}, expected {vector.gas}"
    if failures = 0 then
      IO.println s!"PASS {vectors.size} official vectors"
      return 0
    else
      IO.eprintln s!"FAIL {failures} mismatch(es)"
      return 1
