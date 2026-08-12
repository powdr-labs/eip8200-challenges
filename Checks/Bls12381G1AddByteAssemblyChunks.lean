import Challenge.Bls12381G1Add.Reference.Proofs.ByteAssembly

set_option warningAsError true

open Challenge.Bls12381G1Add.Reference.Proofs.Compilation

example : referenceInstructionBytesChunk 0 = referenceFrozenBytesChunk 0 :=
  referenceInstructionBytesChunk0

example :
    referenceInstructionBytesChunk 0 = referenceFrozenBytesChunk 0 ∧
    referenceInstructionBytesChunk 1 = referenceFrozenBytesChunk 1 ∧
    referenceInstructionBytesChunk 2 = referenceFrozenBytesChunk 2 ∧
    referenceInstructionBytesChunk 3 = referenceFrozenBytesChunk 3 ∧
    referenceInstructionBytesChunk 4 = referenceFrozenBytesChunk 4 ∧
    referenceInstructionBytesChunk 5 = referenceFrozenBytesChunk 5 ∧
    referenceInstructionBytesChunk 6 = referenceFrozenBytesChunk 6 ∧
    referenceInstructionBytesChunk 7 = referenceFrozenBytesChunk 7 ∧
    referenceInstructionBytesChunk 8 = referenceFrozenBytesChunk 8 ∧
    referenceInstructionBytesChunk 9 = referenceFrozenBytesChunk 9 ∧
    referenceInstructionBytesChunk 10 = referenceFrozenBytesChunk 10 :=
  referenceInstructionByteChunkChecks

example : YulEvmCompiler.assemble referenceInstructions =
    Challenge.Bls12381G1Add.referenceBytecode :=
  referenceInstructions_assemble

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.Compilation.referenceInstructionBytesChunk0' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms referenceInstructionBytesChunk0

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.Compilation.referenceInstructionBytesChunk1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms referenceInstructionBytesChunk1

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.Compilation.referenceInstructionBytesChunk2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms referenceInstructionBytesChunk2

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.Compilation.referenceInstructionBytesChunk3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms referenceInstructionBytesChunk3

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.Compilation.referenceInstructionBytesChunk4' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms referenceInstructionBytesChunk4

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.Compilation.referenceInstructionBytesChunk5' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms referenceInstructionBytesChunk5

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.Compilation.referenceInstructionBytesChunk6' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms referenceInstructionBytesChunk6

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.Compilation.referenceInstructionBytesChunk7' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms referenceInstructionBytesChunk7

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.Compilation.referenceInstructionBytesChunk8' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms referenceInstructionBytesChunk8

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.Compilation.referenceInstructionBytesChunk9' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms referenceInstructionBytesChunk9

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.Compilation.referenceInstructionBytesChunk10' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms referenceInstructionBytesChunk10

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.Compilation.referenceInstructionByteChunkChecks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms referenceInstructionByteChunkChecks

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.Compilation.referenceInstructions_assemble' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms referenceInstructions_assemble

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.Compilation.referenceBytecode_size_lt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms referenceBytecode_size_lt
