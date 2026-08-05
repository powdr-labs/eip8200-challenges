import Challenge.EvmProof.Stepper
import Challenge.Ripemd160.Reference.Bytecode
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
/-!
# Structural certificate for the frozen RIPEMD-160 artifact

The instruction-boundary list below is generated from the reusable raw-bytecode
disassembler. Its assembly theorem ties every location used by the direct proof
to the exact frozen bytes.
-/

namespace Challenge.Ripemd160.Reference.Proofs.Bytecode.Artifact

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

def op (opcode : UInt8) : Instr :=
  match Decode.opcodeOf opcode with
  | some decoded => .op decoded
  | none => .op .INVALID

def referenceInstructions : List Instr :=
[
  .push 31 1780731860627700044960722568376592188711674974810043212252563479055960840,
  .push 2 1184,
  op 0x52,
  .push 32 1374703749640218873849524064026661036561295975619335768036000015621818746370,
  .push 2 1216,
  op 0x52,
  .push 32 1809286146446445343010337679715913357291520642540487409382712519614204477440,
  .push 2 1248,
  op 0x52,
  .push 32 2286348414996307935469207465186628553155355030353023797310855598864584999170,
  .push 2 1280,
  op 0x52,
  .push 32 6793533947442029545286681365244130742947859423983440781638017424580845963790,
  .push 2 1312,
  op 0x52,
  .push 32 5454326014381509071620663843103927214778145566039445656282506490595801825280,
  .push 2 1344,
  op 0x52,
  .push 32 5000281043567253289773844389228683908720941172611121566642559091978571025676,
  .push 2 1376,
  op 0x52,
  .push 32 4998451946933852135137276647445154408072640462072745561656555001729660617996,
  .push 2 1408,
  op 0x52,
  .push 32 4097353149147406276549177442451244923784709130172834976461593227075946283008,
  .push 2 1440,
  op 0x52,
  .push 32 3634466825900925589093651101374881051901026410458987220032629834781140389131,
  .push 2 1472,
  op 0x52,
  .push 32 4083287390302437702768465126624575726298108573653391417181074648310269415176,
  .push 2 1504,
  op 0x52,
  .push 32 3627420088851531435467691758328083203359072412578514691593700216701345333248,
  .push 2 1536,
  op 0x52,
  .push 0 0,
  .push 2 1568,
  op 0x52,
  .push 4 1518500249,
  .push 2 1600,
  op 0x52,
  .push 4 1859775393,
  .push 2 1632,
  op 0x52,
  .push 4 2400959708,
  .push 2 1664,
  op 0x52,
  .push 4 2840853838,
  .push 2 1696,
  op 0x52,
  .push 4 1352829926,
  .push 2 1728,
  op 0x52,
  .push 4 1548603684,
  .push 2 1760,
  op 0x52,
  .push 4 1836072691,
  .push 2 1792,
  op 0x52,
  .push 4 2053994217,
  .push 2 1824,
  op 0x52,
  .push 0 0,
  .push 2 1856,
  op 0x52,
  .push 4 1732584193,
  .push 1 32,
  op 0x52,
  .push 4 4023233417,
  .push 1 64,
  op 0x52,
  .push 4 2562383102,
  .push 1 96,
  op 0x52,
  .push 4 271733878,
  .push 1 128,
  op 0x52,
  .push 4 3285377520,
  .push 1 160,
  op 0x52,
  op 0x36,
  .push 1 72,
  op 0x81,
  op 0x01,
  .push 1 6,
  op 0x1c,
  .push 1 6,
  op 0x1b,
  .push 0 0,
  .push 2 2048,
  op 0x83,
  op 0x91,
  op 0x90,
  op 0x37,
  .push 1 128,
  .push 2 2048,
  op 0x83,
  op 0x01,
  op 0x53,
  .push 1 3,
  op 0x90,
  op 0x91,
  op 0x90,
  op 0x1b,
  .push 1 8,
  op 0x82,
  op 0x03,
  .push 2 2048,
  op 0x01,
  .push 0 0,
  .push 2 694,
  op 0x56,
  op 0x5b,
  op 0x80,
  op 0x82,
  op 0x11,
  .push 2 634,
  op 0x57,
  op 0x50,
  op 0x50,
  .push 0 0,
  .push 0 0,
  op 0x52,
  .push 0 0,
  .push 2 645,
  op 0x56,
  op 0xfe,
  .push 2 1688,
  op 0x56,
  op 0x5b,
  .push 2 2048,
  op 0x81,
  op 0x01,
  .push 0 0,
  .push 2 1114,
  op 0x56,
  op 0x5b,
  .push 1 5,
  op 0x81,
  op 0x10,
  .push 2 668,
  op 0x57,
  op 0x50,
  .push 1 32,
  .push 0 0,
  op 0xf3,
  .push 2 1688,
  op 0x56,
  op 0xfe,
  .push 2 1688,
  op 0x56,
  op 0x5b,
  op 0x80,
  .push 1 5,
  op 0x1b,
  .push 1 32,
  op 0x01,
  op 0x51,
  op 0x81,
  .push 1 2,
  op 0x1b,
  .push 1 12,
  op 0x01,
  .push 0 0,
  .push 2 1248,
  op 0x56,
  op 0xfe,
  .push 2 1688,
  op 0x56,
  op 0x5b,
  .push 1 8,
  op 0x81,
  op 0x10,
  .push 2 716,
  op 0x57,
  op 0x50,
  op 0x50,
  op 0x50,
  .push 0 0,
  .push 2 611,
  op 0x56,
  op 0xfe,
  .push 2 1688,
  op 0x56,
  op 0x5b,
  .push 1 255,
  op 0x81,
  .push 1 3,
  op 0x1b,
  op 0x84,
  op 0x90,
  op 0x1c,
  op 0x16,
  op 0x82,
  op 0x82,
  op 0x01,
  op 0x53,
  .push 1 1,
  op 0x01,
  .push 2 694,
  op 0x56,
  op 0xfe,
  .push 2 1688,
  op 0x56,
  op 0xfe,
  .push 2 1688,
  op 0x56,
  op 0x5b,
  .push 1 80,
  op 0x81,
  op 0x10,
  .push 2 768,
  op 0x57,
  op 0x50,
  .push 0 0,
  .push 2 844,
  op 0x56,
  op 0xfe,
  .push 2 1688,
  op 0x56,
  op 0x5b,
  op 0x80,
  .push 1 4,
  op 0x1c,
  op 0x80,
  .push 1 5,
  op 0x1b,
  .push 2 1568,
  op 0x01,
  op 0x51,
  .push 2 1376,
  op 0x83,
  .push 1 5,
  op 0x1c,
  .push 1 5,
  op 0x1b,
  op 0x01,
  op 0x51,
  .push 1 31,
  op 0x84,
  op 0x16,
  op 0x1a,
  .push 2 1184,
  op 0x84,
  .push 1 5,
  op 0x1c,
  .push 1 5,
  op 0x1b,
  op 0x01,
  op 0x51,
  .push 1 31,
  op 0x85,
  op 0x16,
  op 0x1a,
  .push 1 192,
  .push 2 830,
  op 0x84,
  op 0x84,
  op 0x84,
  op 0x88,
  op 0x85,
  .push 2 1339,
  op 0x56,
  op 0x5b,
  op 0x50,
  op 0x50,
  op 0x50,
  op 0x50,
  .push 1 1,
  op 0x90,
  op 0x50,
  op 0x01,
  .push 2 748,
  op 0x56,
  op 0x5b,
  .push 1 80,
  op 0x81,
  op 0x10,
  .push 2 1009,
  op 0x57,
  op 0x50,
  .push 2 448,
  op 0x51,
  .push 2 256,
  op 0x51,
  .push 2 544,
  op 0x51,
  op 0x01,
  op 0x01,
  .push 4 4294967295,
  op 0x16,
  .push 2 480,
  op 0x51,
  .push 2 288,
  op 0x51,
  .push 2 576,
  op 0x51,
  op 0x01,
  op 0x01,
  .push 4 4294967295,
  op 0x16,
  .push 4 4294967295,
  op 0x16,
  .push 1 64,
  op 0x52,
  .push 2 352,
  op 0x51,
  .push 2 320,
  op 0x51,
  .push 2 608,
  op 0x51,
  op 0x01,
  op 0x01,
  .push 4 4294967295,
  op 0x16,
  .push 4 4294967295,
  op 0x16,
  .push 1 96,
  op 0x52,
  .push 2 384,
  op 0x51,
  .push 1 192,
  op 0x51,
  .push 2 640,
  op 0x51,
  op 0x01,
  op 0x01,
  .push 4 4294967295,
  op 0x16,
  .push 4 4294967295,
  op 0x16,
  .push 1 128,
  op 0x52,
  .push 2 416,
  op 0x51,
  .push 1 224,
  op 0x51,
  .push 2 512,
  op 0x51,
  op 0x01,
  op 0x01,
  .push 4 4294967295,
  op 0x16,
  .push 4 4294967295,
  op 0x16,
  .push 1 160,
  op 0x52,
  .push 4 4294967295,
  op 0x16,
  .push 1 32,
  op 0x52,
  .push 1 64,
  op 0x01,
  .push 2 611,
  op 0x56,
  op 0xfe,
  .push 2 1688,
  op 0x56,
  op 0x5b,
  op 0x80,
  .push 1 4,
  op 0x1c,
  op 0x80,
  .push 1 5,
  op 0x1b,
  .push 2 1728,
  op 0x01,
  op 0x51,
  .push 2 1472,
  op 0x83,
  .push 1 5,
  op 0x1c,
  .push 1 5,
  op 0x1b,
  op 0x01,
  op 0x51,
  .push 1 31,
  op 0x84,
  op 0x16,
  op 0x1a,
  .push 2 1280,
  op 0x84,
  .push 1 5,
  op 0x1c,
  .push 1 5,
  op 0x1b,
  op 0x01,
  op 0x51,
  .push 1 31,
  op 0x85,
  op 0x16,
  op 0x1a,
  .push 1 4,
  op 0x90,
  op 0x91,
  op 0x92,
  op 0x93,
  op 0x90,
  op 0x03,
  .push 2 352,
  .push 2 1080,
  op 0x85,
  op 0x85,
  op 0x85,
  op 0x85,
  op 0x85,
  .push 2 1339,
  op 0x56,
  op 0x5b,
  op 0x50,
  op 0x50,
  op 0x50,
  op 0x50,
  .push 1 1,
  op 0x90,
  op 0x50,
  op 0x01,
  .push 2 844,
  op 0x56,
  op 0xfe,
  .push 2 1688,
  op 0x56,
  op 0xfe,
  .push 2 1688,
  op 0x56,
  op 0xfe,
  .push 2 1688,
  op 0x56,
  op 0xfe,
  .push 2 1688,
  op 0x56,
  op 0x5b,
  .push 1 16,
  op 0x81,
  op 0x10,
  .push 2 1158,
  op 0x57,
  op 0x50,
  op 0x50,
  .push 1 160,
  .push 1 32,
  .push 1 192,
  op 0x5e,
  .push 1 160,
  .push 1 32,
  .push 2 352,
  op 0x5e,
  .push 1 160,
  .push 1 32,
  .push 2 512,
  op 0x5e,
  .push 0 0,
  .push 2 748,
  op 0x56,
  op 0xfe,
  .push 2 1688,
  op 0x56,
  op 0x5b,
  op 0x80,
  .push 1 2,
  op 0x1b,
  op 0x82,
  op 0x01,
  op 0x51,
  op 0x80,
  .push 1 3,
  op 0x1a,
  .push 1 24,
  op 0x1b,
  op 0x81,
  .push 1 2,
  op 0x1a,
  .push 1 16,
  op 0x1b,
  op 0x17,
  op 0x81,
  .push 1 1,
  op 0x1a,
  .push 1 8,
  op 0x1b,
  .push 0 0,
  op 0x90,
  op 0x91,
  op 0x92,
  op 0x90,
  op 0x1a,
  op 0x17,
  op 0x17,
  .push 4 4294967295,
  op 0x16,
  op 0x81,
  .push 1 5,
  op 0x1b,
  .push 2 672,
  op 0x01,
  op 0x52,
  .push 1 1,
  op 0x01,
  .push 2 1114,
  op 0x56,
  op 0xfe,
  .push 2 1688,
  op 0x56,
  op 0xfe,
  .push 2 1688,
  op 0x56,
  op 0xfe,
  .push 2 1688,
  op 0x56,
  op 0xfe,
  .push 2 1688,
  op 0x56,
  op 0xfe,
  .push 2 1688,
  op 0x56,
  op 0xfe,
  .push 2 1688,
  op 0x56,
  op 0x5b,
  .push 1 4,
  op 0x81,
  op 0x10,
  .push 2 1272,
  op 0x57,
  op 0x50,
  op 0x50,
  op 0x50,
  .push 1 1,
  op 0x01,
  .push 2 645,
  op 0x56,
  op 0xfe,
  .push 2 1688,
  op 0x56,
  op 0x5b,
  .push 1 255,
  op 0x81,
  .push 1 3,
  op 0x1b,
  op 0x84,
  op 0x90,
  op 0x1c,
  op 0x16,
  op 0x82,
  op 0x82,
  op 0x01,
  op 0x53,
  .push 1 1,
  op 0x01,
  .push 2 1248,
  op 0x56,
  op 0xfe,
  .push 2 1688,
  op 0x56,
  op 0xfe,
  .push 2 1688,
  op 0x56,
  op 0xfe,
  .push 2 1688,
  op 0x56,
  op 0xfe,
  .push 2 1688,
  op 0x56,
  op 0xfe,
  .push 2 1688,
  op 0x56,
  op 0xfe,
  .push 2 1688,
  op 0x56,
  op 0xfe,
  .push 2 1688,
  op 0x56,
  op 0xfe,
  .push 2 1688,
  op 0x56,
  op 0xfe,
  .push 2 1688,
  op 0x56,
  op 0x5b,
  op 0x80,
  op 0x51,
  .push 1 32,
  op 0x82,
  op 0x01,
  op 0x51,
  .push 1 64,
  op 0x83,
  op 0x01,
  op 0x51,
  .push 1 96,
  op 0x84,
  op 0x01,
  op 0x51,
  .push 1 128,
  op 0x85,
  op 0x01,
  op 0x51,
  .push 1 5,
  op 0x90,
  op 0x91,
  op 0x92,
  op 0x93,
  op 0x94,
  op 0x95,
  op 0x96,
  op 0x97,
  op 0x90,
  op 0x1b,
  .push 2 672,
  op 0x01,
  op 0x51,
  .push 0 0,
  op 0x88,
  op 0x14,
  .push 2 1401,
  op 0x57,
  op 0x98,
  op 0x92,
  op 0x95,
  op 0x90,
  op 0x97,
  op 0x91,
  op 0x96,
  op 0x90,
  op 0x93,
  op 0x94,
  op 0x93,
  .push 2 1582,
  op 0x56,
  op 0x5b,
  op 0x96,
  op 0x50,
  op 0x90,
  op 0x91,
  op 0x92,
  op 0x93,
  op 0x94,
  op 0x95,
  .push 2 1561,
  op 0x56,
  op 0xfe,
  op 0x56,
  op 0xfe,
  op 0x56,
  op 0xfe,
  op 0x56,
  op 0x5b,
  op 0x90,
  op 0x91,
  op 0x92,
  op 0x93,
  op 0x01,
  op 0x90,
  op 0x91,
  op 0x92,
  op 0x93,
  op 0x94,
  op 0x95,
  op 0x96,
  op 0x97,
  op 0x01,
  op 0x90,
  op 0x91,
  op 0x92,
  op 0x01,
  .push 4 4294967295,
  op 0x16,
  .push 4 4294967295,
  op 0x83,
  .push 1 32,
  op 0x03,
  op 0x82,
  op 0x90,
  op 0x1c,
  op 0x91,
  op 0x90,
  op 0x92,
  op 0x93,
  op 0x1b,
  op 0x17,
  op 0x16,
  op 0x85,
  op 0x01,
  .push 4 4294967295,
  op 0x16,
  .push 4 4294967295,
  op 0x90,
  op 0x91,
  op 0x92,
  op 0x93,
  op 0x94,
  op 0x95,
  op 0x16,
  op 0x82,
  op 0x52,
  .push 4 4294967295,
  op 0x90,
  op 0x91,
  op 0x92,
  op 0x93,
  op 0x94,
  op 0x16,
  .push 1 128,
  op 0x83,
  op 0x01,
  op 0x52,
  .push 1 10,
  .push 4 4294967295,
  op 0x85,
  .push 1 22,
  op 0x1c,
  op 0x91,
  op 0x90,
  op 0x92,
  op 0x93,
  op 0x94,
  op 0x95,
  op 0x90,
  op 0x1b,
  op 0x17,
  op 0x16,
  .push 4 4294967295,
  op 0x16,
  .push 1 96,
  op 0x83,
  op 0x01,
  op 0x52,
  .push 4 4294967295,
  op 0x90,
  op 0x91,
  op 0x92,
  op 0x16,
  .push 1 64,
  op 0x83,
  op 0x01,
  op 0x52,
  .push 4 4294967295,
  op 0x16,
  .push 1 32,
  op 0x90,
  op 0x91,
  op 0x01,
  op 0x52,
  op 0x56,
  op 0x5b,
  op 0x84,
  op 0x84,
  op 0x18,
  op 0x83,
  op 0x18,
  op 0x90,
  op 0x98,
  op 0x92,
  op 0x96,
  op 0x90,
  op 0x91,
  op 0x97,
  op 0x91,
  op 0x93,
  op 0x95,
  op 0x93,
  .push 2 1420,
  op 0x56,
  op 0x5b,
  .push 1 1,
  op 0x82,
  op 0x14,
  op 0x15,
  .push 2 1606,
  op 0x57,
  op 0x90,
  op 0x50,
  op 0x84,
  op 0x19,
  op 0x87,
  op 0x16,
  op 0x85,
  op 0x87,
  op 0x16,
  op 0x17,
  .push 2 1420,
  op 0x56,
  op 0x5b,
  .push 1 2,
  op 0x82,
  op 0x14,
  op 0x15,
  .push 2 1634,
  op 0x57,
  op 0x90,
  op 0x50,
  .push 4 4294967295,
  op 0x86,
  op 0x19,
  op 0x86,
  op 0x17,
  op 0x88,
  op 0x18,
  op 0x16,
  .push 2 1420,
  op 0x56,
  op 0x5b,
  .push 1 3,
  op 0x90,
  op 0x91,
  op 0x14,
  op 0x15,
  .push 2 1657,
  op 0x57,
  op 0x86,
  op 0x19,
  op 0x86,
  op 0x16,
  op 0x85,
  op 0x88,
  op 0x16,
  op 0x17,
  .push 2 1420,
  op 0x56,
  op 0x5b,
  .push 4 4294967295,
  op 0x87,
  op 0x19,
  op 0x87,
  op 0x17,
  op 0x86,
  op 0x18,
  op 0x16,
  .push 2 1420,
  op 0x56,
  op 0xfe,
  op 0x56,
  op 0xfe,
  op 0x56,
  op 0xfe,
  op 0x56,
  op 0xfe,
  op 0x56,
  op 0xfe,
  op 0x56,
  op 0xfe,
  op 0x56,
  op 0xfe,
  op 0x56,
  op 0x5b
]

theorem referenceInstructions_count : referenceInstructions.length = 846 := by
  decide

theorem assemble_referenceInstructions :
    assemble referenceInstructions = referenceBytecode := by
  apply ByteArray.ext
  simp (config := { maxSteps := 1000000 })
    [assemble, assembleBytes, referenceInstructions, op, referenceBytecode,
    referenceBytes, Instr.bytes, natToBE]
  repeat' apply And.intro
  all_goals decide

def referenceArtifact : Challenge.EvmProof.ProgramArtifact where
  code := referenceBytecode
  instructions := referenceInstructions
  assembly_eq := assemble_referenceInstructions

def instructionPC (index : Nat) : Nat :=
  referenceArtifact.instructionPC index

/-- One of the straight-line stores which initializes RIPEMD's lookup tables,
round constants, and five-word initial chaining value. -/
structure InitStore where
  index : Nat
  valueWidth : Fin 33
  value : UInt256
  offsetWidth : Fin 33
  offset : UInt256

def initStores : List InitStore :=
  [⟨0, 31, 0x102030405060708090a0b0c0d0e0f07040d010a060f030c000905020e0b08, 2, 0x4a0⟩,
   ⟨3, 32, 0x30a0e04090f0801020700060d0b050c01090b0a00080c040d03070f0e050602, 2, 0x4c0⟩,
   ⟨6, 32, 0x4000509070c020a0e0103080b060f0d00000000000000000000000000000000, 2, 0x4e0⟩,
   ⟨9, 32, 0x50e070009020b040d060f08010a030c060b0307000d050a0e0f080c04090102, 2, 0x500⟩,
   ⟨12, 32, 0xf050103070e06090b080c020a00040d08060401030b0f00050c020d09070a0e, 2, 0x520⟩,
   ⟨15, 32, 0xc0f0a040105080706020d0e0003090b00000000000000000000000000000000, 2, 0x540⟩,
   ⟨18, 32, 0xb0e0f0c050807090b0d0e0f060709080706080d0b09070f070c0f090b070d0c, 2, 0x560⟩,
   ⟨21, 32, 0xb0d06070e090d0f0e080d06050c07050b0c0e0f0e0f0908090e05060806050c, 2, 0x580⟩,
   ⟨24, 32, 0x90f050b06080d0c050c0d0e0b08050600000000000000000000000000000000, 2, 0x5a0⟩,
   ⟨27, 32, 0x809090b0d0f0f050707080b0e0e0c06090d0f070c08090b07070c07060f0d0b, 2, 0x5c0⟩,
   ⟨30, 32, 0x9070f0b0806060e0c0d050e0d0d07050f05080b0e0e060e06090c090c050f08, 2, 0x5e0⟩,
   ⟨33, 32, 0x8050c090c050e06080d06050f0d0b0b00000000000000000000000000000000, 2, 0x600⟩,
   ⟨36, 0, 0, 2, 0x620⟩,
   ⟨39, 4, 0x5a827999, 2, 0x640⟩,
   ⟨42, 4, 0x6ed9eba1, 2, 0x660⟩,
   ⟨45, 4, 0x8f1bbcdc, 2, 0x680⟩,
   ⟨48, 4, 0xa953fd4e, 2, 0x6a0⟩,
   ⟨51, 4, 0x50a28be6, 2, 0x6c0⟩,
   ⟨54, 4, 0x5c4dd124, 2, 0x6e0⟩,
   ⟨57, 4, 0x6d703ef3, 2, 0x700⟩,
   ⟨60, 4, 0x7a6d76e9, 2, 0x720⟩,
   ⟨63, 0, 0, 2, 0x740⟩,
   ⟨66, 4, 0x67452301, 1, 0x20⟩,
   ⟨69, 4, 0xefcdab89, 1, 0x40⟩,
   ⟨72, 4, 0x98badcfe, 1, 0x60⟩,
   ⟨75, 4, 0x10325476, 1, 0x80⟩,
   ⟨78, 4, 0xc3d2e1f0, 1, 0xa0⟩]

theorem initStore_valid (w : InitStore) (hw : w ∈ initStores) :
    referenceInstructions[w.index]? = some (.push w.valueWidth w.value) ∧
    instructionPC (w.index + 1) = instructionPC w.index + w.valueWidth.val + 1 ∧
    referenceInstructions[w.index + 1]? = some (.push w.offsetWidth w.offset) ∧
    instructionPC (w.index + 2) = instructionPC (w.index + 1) + w.offsetWidth.val + 1 ∧
    referenceInstructions[w.index + 2]? = some (.op .MSTORE) ∧
    instructionPC (w.index + 3) = instructionPC (w.index + 2) + 1 := by
  simp only [initStores, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals repeat' apply And.intro
  all_goals rfl

@[simp] theorem referenceArtifact_pc_683 :
    referenceArtifact.instructionPC 683 = 0x5b9 := by rfl

@[simp] theorem referenceArtifact_pc_684 :
    referenceArtifact.instructionPC 684 = 0x5ba := by rfl

@[simp] theorem referenceArtifact_pc_685 :
    referenceArtifact.instructionPC 685 = 0x5bf := by rfl

@[simp] theorem referenceArtifact_pc_686 :
    referenceArtifact.instructionPC 686 = 0x5c0 := by rfl

@[simp] theorem referenceArtifact_pc_687 :
    referenceArtifact.instructionPC 687 = 0x5c5 := by rfl

@[simp] theorem referenceArtifact_pc_688 :
    referenceArtifact.instructionPC 688 = 0x5c6 := by rfl

@[simp] theorem referenceArtifact_pc_689 :
    referenceArtifact.instructionPC 689 = 0x5c7 := by rfl

@[simp] theorem referenceArtifact_pc_690 :
    referenceArtifact.instructionPC 690 = 0x5c8 := by rfl

@[simp] theorem referenceArtifact_pc_691 :
    referenceArtifact.instructionPC 691 = 0x5c9 := by rfl

@[simp] theorem referenceArtifact_pc_692 :
    referenceArtifact.instructionPC 692 = 0x5ca := by rfl

@[simp] theorem referenceArtifact_pc_693 :
    referenceArtifact.instructionPC 693 = 0x5cb := by rfl

@[simp] theorem referenceArtifact_pc_694 :
    referenceArtifact.instructionPC 694 = 0x5cc := by rfl

@[simp] theorem referenceArtifact_pc_695 :
    referenceArtifact.instructionPC 695 = 0x5cd := by rfl

@[simp] theorem referenceArtifact_pc_696 :
    referenceArtifact.instructionPC 696 = 0x5ce := by rfl

@[simp] theorem referenceArtifact_pc_697 :
    referenceArtifact.instructionPC 697 = 0x5d3 := by rfl

@[simp] theorem referenceArtifact_pc_698 :
    referenceArtifact.instructionPC 698 = 0x5d4 := by rfl

@[simp] theorem referenceArtifact_pc_699 :
    referenceArtifact.instructionPC 699 = 0x5d5 := by rfl

@[simp] theorem referenceArtifact_pc_700 :
    referenceArtifact.instructionPC 700 = 0x5d6 := by rfl

@[simp] theorem referenceArtifact_pc_701 :
    referenceArtifact.instructionPC 701 = 0x5d7 := by rfl

@[simp] theorem referenceArtifact_pc_702 :
    referenceArtifact.instructionPC 702 = 0x5d8 := by rfl

@[simp] theorem referenceArtifact_pc_703 :
    referenceArtifact.instructionPC 703 = 0x5d9 := by rfl

@[simp] theorem referenceArtifact_pc_704 :
    referenceArtifact.instructionPC 704 = 0x5db := by rfl

@[simp] theorem referenceArtifact_pc_705 :
    referenceArtifact.instructionPC 705 = 0x5dc := by rfl

@[simp] theorem referenceArtifact_pc_706 :
    referenceArtifact.instructionPC 706 = 0x5dd := by rfl

@[simp] theorem referenceArtifact_pc_707 :
    referenceArtifact.instructionPC 707 = 0x5de := by rfl

@[simp] theorem referenceArtifact_pc_708 :
    referenceArtifact.instructionPC 708 = 0x5e0 := by rfl

@[simp] theorem referenceArtifact_pc_709 :
    referenceArtifact.instructionPC 709 = 0x5e5 := by rfl

@[simp] theorem referenceArtifact_pc_710 :
    referenceArtifact.instructionPC 710 = 0x5e6 := by rfl

@[simp] theorem referenceArtifact_pc_711 :
    referenceArtifact.instructionPC 711 = 0x5e8 := by rfl

@[simp] theorem referenceArtifact_pc_712 :
    referenceArtifact.instructionPC 712 = 0x5e9 := by rfl

@[simp] theorem referenceArtifact_pc_713 :
    referenceArtifact.instructionPC 713 = 0x5ea := by rfl

@[simp] theorem referenceArtifact_pc_714 :
    referenceArtifact.instructionPC 714 = 0x5eb := by rfl

@[simp] theorem referenceArtifact_pc_715 :
    referenceArtifact.instructionPC 715 = 0x5ec := by rfl

@[simp] theorem referenceArtifact_pc_716 :
    referenceArtifact.instructionPC 716 = 0x5ed := by rfl

@[simp] theorem referenceArtifact_pc_717 :
    referenceArtifact.instructionPC 717 = 0x5ee := by rfl

@[simp] theorem referenceArtifact_pc_718 :
    referenceArtifact.instructionPC 718 = 0x5ef := by rfl

@[simp] theorem referenceArtifact_pc_719 :
    referenceArtifact.instructionPC 719 = 0x5f0 := by rfl

@[simp] theorem referenceArtifact_pc_720 :
    referenceArtifact.instructionPC 720 = 0x5f1 := by rfl

@[simp] theorem referenceArtifact_pc_721 :
    referenceArtifact.instructionPC 721 = 0x5f2 := by rfl

@[simp] theorem referenceArtifact_pc_722 :
    referenceArtifact.instructionPC 722 = 0x5f3 := by rfl

@[simp] theorem referenceArtifact_pc_723 :
    referenceArtifact.instructionPC 723 = 0x5f8 := by rfl

@[simp] theorem referenceArtifact_pc_724 :
    referenceArtifact.instructionPC 724 = 0x5f9 := by rfl

@[simp] theorem referenceArtifact_pc_725 :
    referenceArtifact.instructionPC 725 = 0x5fb := by rfl

@[simp] theorem referenceArtifact_pc_726 :
    referenceArtifact.instructionPC 726 = 0x5fc := by rfl

@[simp] theorem referenceArtifact_pc_727 :
    referenceArtifact.instructionPC 727 = 0x5fd := by rfl

@[simp] theorem referenceArtifact_pc_728 :
    referenceArtifact.instructionPC 728 = 0x5fe := by rfl

@[simp] theorem referenceArtifact_pc_729 :
    referenceArtifact.instructionPC 729 = 0x603 := by rfl

@[simp] theorem referenceArtifact_pc_730 :
    referenceArtifact.instructionPC 730 = 0x604 := by rfl

@[simp] theorem referenceArtifact_pc_731 :
    referenceArtifact.instructionPC 731 = 0x605 := by rfl

@[simp] theorem referenceArtifact_pc_732 :
    referenceArtifact.instructionPC 732 = 0x606 := by rfl

@[simp] theorem referenceArtifact_pc_733 :
    referenceArtifact.instructionPC 733 = 0x607 := by rfl

@[simp] theorem referenceArtifact_pc_734 :
    referenceArtifact.instructionPC 734 = 0x609 := by rfl

@[simp] theorem referenceArtifact_pc_735 :
    referenceArtifact.instructionPC 735 = 0x60a := by rfl

@[simp] theorem referenceArtifact_pc_736 :
    referenceArtifact.instructionPC 736 = 0x60b := by rfl

@[simp] theorem referenceArtifact_pc_737 :
    referenceArtifact.instructionPC 737 = 0x60c := by rfl

@[simp] theorem referenceArtifact_pc_738 :
    referenceArtifact.instructionPC 738 = 0x611 := by rfl

@[simp] theorem referenceArtifact_pc_739 :
    referenceArtifact.instructionPC 739 = 0x612 := by rfl

@[simp] theorem referenceArtifact_pc_740 :
    referenceArtifact.instructionPC 740 = 0x614 := by rfl

@[simp] theorem referenceArtifact_pc_741 :
    referenceArtifact.instructionPC 741 = 0x615 := by rfl

@[simp] theorem referenceArtifact_pc_742 :
    referenceArtifact.instructionPC 742 = 0x616 := by rfl

@[simp] theorem referenceArtifact_pc_743 :
    referenceArtifact.instructionPC 743 = 0x617 := by rfl

@[simp] theorem referenceArtifact_pc_744 :
    referenceArtifact.instructionPC 744 = 0x618 := by rfl

@[simp] theorem referenceArtifact_pc_745 :
    referenceArtifact.instructionPC 745 = 0x619 := by rfl

@[simp] theorem referenceArtifact_pc_746 :
    referenceArtifact.instructionPC 746 = 0x61a := by rfl

@[simp] theorem referenceArtifact_pc_747 :
    referenceArtifact.instructionPC 747 = 0x61b := by rfl

@[simp] theorem referenceArtifact_pc_748 :
    referenceArtifact.instructionPC 748 = 0x61c := by rfl

@[simp] theorem referenceArtifact_pc_749 :
    referenceArtifact.instructionPC 749 = 0x61d := by rfl

@[simp] theorem referenceArtifact_pc_750 :
    referenceArtifact.instructionPC 750 = 0x61e := by rfl

@[simp] theorem referenceArtifact_pc_751 :
    referenceArtifact.instructionPC 751 = 0x61f := by rfl

@[simp] theorem referenceArtifact_pc_752 :
    referenceArtifact.instructionPC 752 = 0x620 := by rfl

@[simp] theorem referenceArtifact_pc_753 :
    referenceArtifact.instructionPC 753 = 0x621 := by rfl

@[simp] theorem referenceArtifact_pc_754 :
    referenceArtifact.instructionPC 754 = 0x622 := by rfl

@[simp] theorem referenceArtifact_pc_755 :
    referenceArtifact.instructionPC 755 = 0x623 := by rfl

@[simp] theorem referenceArtifact_pc_756 :
    referenceArtifact.instructionPC 756 = 0x624 := by rfl

@[simp] theorem referenceArtifact_pc_757 :
    referenceArtifact.instructionPC 757 = 0x625 := by rfl

@[simp] theorem referenceArtifact_pc_758 :
    referenceArtifact.instructionPC 758 = 0x626 := by rfl

@[simp] theorem referenceArtifact_pc_759 :
    referenceArtifact.instructionPC 759 = 0x627 := by rfl

@[simp] theorem referenceArtifact_pc_760 :
    referenceArtifact.instructionPC 760 = 0x628 := by rfl

@[simp] theorem referenceArtifact_pc_761 :
    referenceArtifact.instructionPC 761 = 0x629 := by rfl

@[simp] theorem referenceArtifact_pc_762 :
    referenceArtifact.instructionPC 762 = 0x62a := by rfl

@[simp] theorem referenceArtifact_pc_763 :
    referenceArtifact.instructionPC 763 = 0x62d := by rfl


@[simp] theorem referenceArtifact_pc_764 :
    referenceArtifact.instructionPC 764 = 0x62e := by rfl

@[simp] theorem referenceArtifact_pc_765 :
    referenceArtifact.instructionPC 765 = 0x62f := by rfl

@[simp] theorem referenceArtifact_pc_766 :
    referenceArtifact.instructionPC 766 = 0x631 := by rfl

@[simp] theorem referenceArtifact_pc_767 :
    referenceArtifact.instructionPC 767 = 0x632 := by rfl

@[simp] theorem referenceArtifact_pc_0 :
    referenceArtifact.instructionPC 0 = 0x0 := by rfl

@[simp] theorem referenceArtifact_pc_1 :
    referenceArtifact.instructionPC 1 = 0x20 := by rfl

@[simp] theorem referenceArtifact_pc_20 :
    referenceArtifact.instructionPC 20 = 0x101 := by rfl

@[simp] theorem referenceArtifact_pc_21 :
    referenceArtifact.instructionPC 21 = 0x102 := by rfl

@[simp] theorem referenceArtifact_pc_22 :
    referenceArtifact.instructionPC 22 = 0x123 := by rfl

@[simp] theorem referenceArtifact_pc_35 :
    referenceArtifact.instructionPC 35 = 0x1ba := by rfl

@[simp] theorem referenceArtifact_pc_36 :
    referenceArtifact.instructionPC 36 = 0x1bb := by rfl

@[simp] theorem referenceArtifact_pc_37 :
    referenceArtifact.instructionPC 37 = 0x1bc := by rfl

@[simp] theorem referenceArtifact_pc_52 :
    referenceArtifact.instructionPC 52 = 0x1e9 := by rfl

@[simp] theorem referenceArtifact_pc_53 :
    referenceArtifact.instructionPC 53 = 0x1ec := by rfl

@[simp] theorem referenceArtifact_pc_54 :
    referenceArtifact.instructionPC 54 = 0x1ed := by rfl

@[simp] theorem referenceArtifact_pc_67 :
    referenceArtifact.instructionPC 67 = 0x212 := by rfl

@[simp] theorem referenceArtifact_pc_68 :
    referenceArtifact.instructionPC 68 = 0x214 := by rfl

@[simp] theorem referenceArtifact_pc_69 :
    referenceArtifact.instructionPC 69 = 0x215 := by rfl

@[simp] theorem referenceArtifact_pc_83 :
    referenceArtifact.instructionPC 83 = 0x238 := by rfl

@[simp] theorem referenceArtifact_pc_84 :
    referenceArtifact.instructionPC 84 = 0x239 := by rfl

@[simp] theorem referenceArtifact_pc_85 :
    referenceArtifact.instructionPC 85 = 0x23a := by rfl

@[simp] theorem referenceArtifact_pc_105 :
    referenceArtifact.instructionPC 105 = 0x256 := by rfl

@[simp] theorem referenceArtifact_pc_106 :
    referenceArtifact.instructionPC 106 = 0x258 := by rfl

@[simp] theorem referenceArtifact_pc_107 :
    referenceArtifact.instructionPC 107 = 0x259 := by rfl

@[simp] theorem referenceArtifact_pc_205 :
    referenceArtifact.instructionPC 205 = 0x2e7 := by rfl

@[simp] theorem referenceArtifact_pc_206 :
    referenceArtifact.instructionPC 206 = 0x2e8 := by rfl

@[simp] theorem referenceArtifact_pc_207 :
    referenceArtifact.instructionPC 207 = 0x2eb := by rfl

@[simp] theorem referenceArtifact_pc_313 :
    referenceArtifact.instructionPC 313 = 0x394 := by rfl

@[simp] theorem referenceArtifact_pc_314 :
    referenceArtifact.instructionPC 314 = 0x395 := by rfl

@[simp] theorem referenceArtifact_pc_315 :
    referenceArtifact.instructionPC 315 = 0x39a := by rfl

@[simp] theorem referenceArtifact_pc_346 :
    referenceArtifact.instructionPC 346 = 0x3d9 := by rfl

@[simp] theorem referenceArtifact_pc_347 :
    referenceArtifact.instructionPC 347 = 0x3db := by rfl

@[simp] theorem referenceArtifact_pc_348 :
    referenceArtifact.instructionPC 348 = 0x3dc := by rfl

@[simp] theorem referenceArtifact_pc_410 :
    referenceArtifact.instructionPC 410 = 0x439 := by rfl

@[simp] theorem referenceArtifact_pc_411 :
    referenceArtifact.instructionPC 411 = 0x43a := by rfl

@[simp] theorem referenceArtifact_pc_412 :
    referenceArtifact.instructionPC 412 = 0x43b := by rfl

@[simp] theorem referenceArtifact_pc_448 :
    referenceArtifact.instructionPC 448 = 0x474 := by rfl

@[simp] theorem referenceArtifact_pc_449 :
    referenceArtifact.instructionPC 449 = 0x476 := by rfl

@[simp] theorem referenceArtifact_pc_450 :
    referenceArtifact.instructionPC 450 = 0x478 := by rfl

@[simp] theorem referenceArtifact_pc_647 :
    referenceArtifact.instructionPC 647 = 0x58c := by rfl

@[simp] theorem referenceArtifact_pc_648 :
    referenceArtifact.instructionPC 648 = 0x58d := by rfl

@[simp] theorem referenceArtifact_pc_649 :
    referenceArtifact.instructionPC 649 = 0x58e := by rfl

@[simp] theorem referenceArtifact_pc_682 :
    referenceArtifact.instructionPC 682 = 0x5b8 := by rfl

@[simp] theorem validJumpDest_1b :
    Decode.isValidJumpDest referenceBytecode 0x1b = true := by
  have h := referenceArtifact.isValidJumpDest_index 20 (by rfl)
  change Decode.isValidJumpDest referenceBytecode
    (referenceArtifact.instructionPC 20) = true at h
  simpa using h

@[simp] theorem validJumpDest_2e :
    Decode.isValidJumpDest referenceBytecode 0x2e = true := by
  have h := referenceArtifact.isValidJumpDest_index 35 (by rfl)
  change Decode.isValidJumpDest referenceBytecode
    (referenceArtifact.instructionPC 35) = true at h
  simpa using h

@[simp] theorem validJumpDest_46 :
    Decode.isValidJumpDest referenceBytecode 0x46 = true := by
  have h := referenceArtifact.isValidJumpDest_index 52 (by rfl)
  change Decode.isValidJumpDest referenceBytecode
    (referenceArtifact.instructionPC 52) = true at h
  simpa using h

@[simp] theorem validJumpDest_5a :
    Decode.isValidJumpDest referenceBytecode 0x5a = true := by
  have h := referenceArtifact.isValidJumpDest_index 67 (by rfl)
  change Decode.isValidJumpDest referenceBytecode
    (referenceArtifact.instructionPC 67) = true at h
  simpa using h

@[simp] theorem validJumpDest_73 :
    Decode.isValidJumpDest referenceBytecode 0x73 = true := by
  have h := referenceArtifact.isValidJumpDest_index 83 (by rfl)
  change Decode.isValidJumpDest referenceBytecode
    (referenceArtifact.instructionPC 83) = true at h
  simpa using h

@[simp] theorem validJumpDest_8e :
    Decode.isValidJumpDest referenceBytecode 0x8e = true := by
  have h := referenceArtifact.isValidJumpDest_index 105 (by rfl)
  change Decode.isValidJumpDest referenceBytecode
    (referenceArtifact.instructionPC 105) = true at h
  simpa using h

@[simp] theorem validJumpDest_10f :
    Decode.isValidJumpDest referenceBytecode 0x10f = true := by
  have h := referenceArtifact.isValidJumpDest_index 205 (by rfl)
  change Decode.isValidJumpDest referenceBytecode
    (referenceArtifact.instructionPC 205) = true at h
  simpa using h

@[simp] theorem validJumpDest_1b2 :
    Decode.isValidJumpDest referenceBytecode 0x1b2 = true := by
  have h := referenceArtifact.isValidJumpDest_index 313 (by rfl)
  change Decode.isValidJumpDest referenceBytecode
    (referenceArtifact.instructionPC 313) = true at h
  simpa using h

@[simp] theorem validJumpDest_1db :
    Decode.isValidJumpDest referenceBytecode 0x1db = true := by
  have h := referenceArtifact.isValidJumpDest_index 346 (by rfl)
  change Decode.isValidJumpDest referenceBytecode
    (referenceArtifact.instructionPC 346) = true at h
  simpa using h

@[simp] theorem validJumpDest_231 :
    Decode.isValidJumpDest referenceBytecode 0x231 = true := by
  have h := referenceArtifact.isValidJumpDest_index 410 (by rfl)
  change Decode.isValidJumpDest referenceBytecode
    (referenceArtifact.instructionPC 410) = true at h
  simpa using h

@[simp] theorem validJumpDest_268 :
    Decode.isValidJumpDest referenceBytecode 0x268 = true := by
  have h := referenceArtifact.isValidJumpDest_index 448 (by rfl)
  change Decode.isValidJumpDest referenceBytecode
    (referenceArtifact.instructionPC 448) = true at h
  simpa using h

@[simp] theorem validJumpDest_3c1 :
    Decode.isValidJumpDest referenceBytecode 0x3c1 = true := by
  have h := referenceArtifact.isValidJumpDest_index 647 (by rfl)
  change Decode.isValidJumpDest referenceBytecode
    (referenceArtifact.instructionPC 647) = true at h
  simpa using h

@[simp] theorem validJumpDest_3ee :
    Decode.isValidJumpDest referenceBytecode 0x3ee = true := by
  have h := referenceArtifact.isValidJumpDest_index 682 (by rfl)
  change Decode.isValidJumpDest referenceBytecode
    (referenceArtifact.instructionPC 682) = true at h
  simpa using h

@[simp] theorem refPc349 :
    referenceArtifact.instructionPC 349 = 0x3e1 := by rfl
@[simp] theorem pc349 :
    instructionPC 349 = 0x3e1 := by rfl

@[simp] theorem refPc350 :
    referenceArtifact.instructionPC 350 = 0x3e2 := by rfl
@[simp] theorem pc350 :
    instructionPC 350 = 0x3e2 := by rfl

@[simp] theorem refPc351 :
    referenceArtifact.instructionPC 351 = 0x3e4 := by rfl
@[simp] theorem pc351 :
    instructionPC 351 = 0x3e4 := by rfl

@[simp] theorem refPc352 :
    referenceArtifact.instructionPC 352 = 0x3e5 := by rfl
@[simp] theorem pc352 :
    instructionPC 352 = 0x3e5 := by rfl

@[simp] theorem refPc353 :
    referenceArtifact.instructionPC 353 = 0x3e7 := by rfl
@[simp] theorem pc353 :
    instructionPC 353 = 0x3e7 := by rfl

@[simp] theorem refPc354 :
    referenceArtifact.instructionPC 354 = 0x3e8 := by rfl
@[simp] theorem pc354 :
    instructionPC 354 = 0x3e8 := by rfl

@[simp] theorem refPc355 :
    referenceArtifact.instructionPC 355 = 0x3eb := by rfl
@[simp] theorem pc355 :
    instructionPC 355 = 0x3eb := by rfl

@[simp] theorem refPc356 :
    referenceArtifact.instructionPC 356 = 0x3ec := by rfl
@[simp] theorem pc356 :
    instructionPC 356 = 0x3ec := by rfl

@[simp] theorem refPc357 :
    referenceArtifact.instructionPC 357 = 0x3ed := by rfl
@[simp] theorem pc357 :
    instructionPC 357 = 0x3ed := by rfl

@[simp] theorem refPc358 :
    referenceArtifact.instructionPC 358 = 0x3f0 := by rfl
@[simp] theorem pc358 :
    instructionPC 358 = 0x3f0 := by rfl

@[simp] theorem refPc359 :
    referenceArtifact.instructionPC 359 = 0x3f1 := by rfl
@[simp] theorem pc359 :
    instructionPC 359 = 0x3f1 := by rfl

@[simp] theorem refPc360 :
    referenceArtifact.instructionPC 360 = 0x3f2 := by rfl
@[simp] theorem pc360 :
    instructionPC 360 = 0x3f2 := by rfl

@[simp] theorem refPc361 :
    referenceArtifact.instructionPC 361 = 0x3f3 := by rfl
@[simp] theorem pc361 :
    instructionPC 361 = 0x3f3 := by rfl

@[simp] theorem refPc362 :
    referenceArtifact.instructionPC 362 = 0x3f5 := by rfl
@[simp] theorem pc362 :
    instructionPC 362 = 0x3f5 := by rfl

@[simp] theorem refPc363 :
    referenceArtifact.instructionPC 363 = 0x3f6 := by rfl
@[simp] theorem pc363 :
    instructionPC 363 = 0x3f6 := by rfl

@[simp] theorem refPc364 :
    referenceArtifact.instructionPC 364 = 0x3f7 := by rfl
@[simp] theorem pc364 :
    instructionPC 364 = 0x3f7 := by rfl

@[simp] theorem refPc365 :
    referenceArtifact.instructionPC 365 = 0x3f9 := by rfl
@[simp] theorem pc365 :
    instructionPC 365 = 0x3f9 := by rfl

@[simp] theorem refPc366 :
    referenceArtifact.instructionPC 366 = 0x3fa := by rfl
@[simp] theorem pc366 :
    instructionPC 366 = 0x3fa := by rfl

@[simp] theorem refPc367 :
    referenceArtifact.instructionPC 367 = 0x3fd := by rfl
@[simp] theorem pc367 :
    instructionPC 367 = 0x3fd := by rfl

@[simp] theorem refPc368 :
    referenceArtifact.instructionPC 368 = 0x3fe := by rfl
@[simp] theorem pc368 :
    instructionPC 368 = 0x3fe := by rfl

@[simp] theorem refPc369 :
    referenceArtifact.instructionPC 369 = 0x3ff := by rfl
@[simp] theorem pc369 :
    instructionPC 369 = 0x3ff := by rfl

@[simp] theorem refPc370 :
    referenceArtifact.instructionPC 370 = 0x402 := by rfl
@[simp] theorem pc370 :
    instructionPC 370 = 0x402 := by rfl

@[simp] theorem refPc371 :
    referenceArtifact.instructionPC 371 = 0x403 := by rfl
@[simp] theorem pc371 :
    instructionPC 371 = 0x403 := by rfl

@[simp] theorem refPc372 :
    referenceArtifact.instructionPC 372 = 0x405 := by rfl
@[simp] theorem pc372 :
    instructionPC 372 = 0x405 := by rfl

@[simp] theorem refPc373 :
    referenceArtifact.instructionPC 373 = 0x406 := by rfl
@[simp] theorem pc373 :
    instructionPC 373 = 0x406 := by rfl

@[simp] theorem refPc374 :
    referenceArtifact.instructionPC 374 = 0x408 := by rfl
@[simp] theorem pc374 :
    instructionPC 374 = 0x408 := by rfl

@[simp] theorem refPc375 :
    referenceArtifact.instructionPC 375 = 0x409 := by rfl
@[simp] theorem pc375 :
    instructionPC 375 = 0x409 := by rfl

@[simp] theorem refPc376 :
    referenceArtifact.instructionPC 376 = 0x40a := by rfl
@[simp] theorem pc376 :
    instructionPC 376 = 0x40a := by rfl

@[simp] theorem refPc377 :
    referenceArtifact.instructionPC 377 = 0x40b := by rfl
@[simp] theorem pc377 :
    instructionPC 377 = 0x40b := by rfl

@[simp] theorem refPc378 :
    referenceArtifact.instructionPC 378 = 0x40d := by rfl
@[simp] theorem pc378 :
    instructionPC 378 = 0x40d := by rfl

@[simp] theorem refPc379 :
    referenceArtifact.instructionPC 379 = 0x40e := by rfl
@[simp] theorem pc379 :
    instructionPC 379 = 0x40e := by rfl

@[simp] theorem refPc380 :
    referenceArtifact.instructionPC 380 = 0x40f := by rfl
@[simp] theorem pc380 :
    instructionPC 380 = 0x40f := by rfl

@[simp] theorem refPc381 :
    referenceArtifact.instructionPC 381 = 0x410 := by rfl
@[simp] theorem pc381 :
    instructionPC 381 = 0x410 := by rfl

@[simp] theorem refPc382 :
    referenceArtifact.instructionPC 382 = 0x413 := by rfl
@[simp] theorem pc382 :
    instructionPC 382 = 0x413 := by rfl

@[simp] theorem refPc383 :
    referenceArtifact.instructionPC 383 = 0x414 := by rfl
@[simp] theorem pc383 :
    instructionPC 383 = 0x414 := by rfl

@[simp] theorem refPc384 :
    referenceArtifact.instructionPC 384 = 0x416 := by rfl
@[simp] theorem pc384 :
    instructionPC 384 = 0x416 := by rfl

@[simp] theorem refPc385 :
    referenceArtifact.instructionPC 385 = 0x417 := by rfl
@[simp] theorem pc385 :
    instructionPC 385 = 0x417 := by rfl

@[simp] theorem refPc386 :
    referenceArtifact.instructionPC 386 = 0x419 := by rfl
@[simp] theorem pc386 :
    instructionPC 386 = 0x419 := by rfl

@[simp] theorem refPc387 :
    referenceArtifact.instructionPC 387 = 0x41a := by rfl
@[simp] theorem pc387 :
    instructionPC 387 = 0x41a := by rfl

@[simp] theorem refPc388 :
    referenceArtifact.instructionPC 388 = 0x41b := by rfl
@[simp] theorem pc388 :
    instructionPC 388 = 0x41b := by rfl

@[simp] theorem refPc389 :
    referenceArtifact.instructionPC 389 = 0x41c := by rfl
@[simp] theorem pc389 :
    instructionPC 389 = 0x41c := by rfl

@[simp] theorem refPc390 :
    referenceArtifact.instructionPC 390 = 0x41e := by rfl
@[simp] theorem pc390 :
    instructionPC 390 = 0x41e := by rfl

@[simp] theorem refPc391 :
    referenceArtifact.instructionPC 391 = 0x41f := by rfl
@[simp] theorem pc391 :
    instructionPC 391 = 0x41f := by rfl

@[simp] theorem refPc392 :
    referenceArtifact.instructionPC 392 = 0x420 := by rfl
@[simp] theorem pc392 :
    instructionPC 392 = 0x420 := by rfl

@[simp] theorem refPc393 :
    referenceArtifact.instructionPC 393 = 0x421 := by rfl
@[simp] theorem pc393 :
    instructionPC 393 = 0x421 := by rfl

@[simp] theorem refPc394 :
    referenceArtifact.instructionPC 394 = 0x423 := by rfl
@[simp] theorem pc394 :
    instructionPC 394 = 0x423 := by rfl

@[simp] theorem refPc395 :
    referenceArtifact.instructionPC 395 = 0x424 := by rfl
@[simp] theorem pc395 :
    instructionPC 395 = 0x424 := by rfl

@[simp] theorem refPc396 :
    referenceArtifact.instructionPC 396 = 0x425 := by rfl
@[simp] theorem pc396 :
    instructionPC 396 = 0x425 := by rfl

@[simp] theorem refPc397 :
    referenceArtifact.instructionPC 397 = 0x426 := by rfl
@[simp] theorem pc397 :
    instructionPC 397 = 0x426 := by rfl

@[simp] theorem refPc398 :
    referenceArtifact.instructionPC 398 = 0x427 := by rfl
@[simp] theorem pc398 :
    instructionPC 398 = 0x427 := by rfl

@[simp] theorem refPc399 :
    referenceArtifact.instructionPC 399 = 0x428 := by rfl
@[simp] theorem pc399 :
    instructionPC 399 = 0x428 := by rfl

@[simp] theorem refPc400 :
    referenceArtifact.instructionPC 400 = 0x429 := by rfl
@[simp] theorem pc400 :
    instructionPC 400 = 0x429 := by rfl

@[simp] theorem refPc401 :
    referenceArtifact.instructionPC 401 = 0x42c := by rfl
@[simp] theorem pc401 :
    instructionPC 401 = 0x42c := by rfl

@[simp] theorem refPc402 :
    referenceArtifact.instructionPC 402 = 0x42f := by rfl
@[simp] theorem pc402 :
    instructionPC 402 = 0x42f := by rfl

@[simp] theorem refPc403 :
    referenceArtifact.instructionPC 403 = 0x430 := by rfl
@[simp] theorem pc403 :
    instructionPC 403 = 0x430 := by rfl

@[simp] theorem refPc404 :
    referenceArtifact.instructionPC 404 = 0x431 := by rfl
@[simp] theorem pc404 :
    instructionPC 404 = 0x431 := by rfl

@[simp] theorem refPc405 :
    referenceArtifact.instructionPC 405 = 0x432 := by rfl
@[simp] theorem pc405 :
    instructionPC 405 = 0x432 := by rfl

@[simp] theorem refPc406 :
    referenceArtifact.instructionPC 406 = 0x433 := by rfl
@[simp] theorem pc406 :
    instructionPC 406 = 0x433 := by rfl

@[simp] theorem refPc407 :
    referenceArtifact.instructionPC 407 = 0x434 := by rfl
@[simp] theorem pc407 :
    instructionPC 407 = 0x434 := by rfl

@[simp] theorem refPc408 :
    referenceArtifact.instructionPC 408 = 0x437 := by rfl
@[simp] theorem pc408 :
    instructionPC 408 = 0x437 := by rfl

@[simp] theorem refPc409 :
    referenceArtifact.instructionPC 409 = 0x438 := by rfl
@[simp] theorem pc409 :
    instructionPC 409 = 0x438 := by rfl

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

/-- Cached located path for the main-body call into `pad`. -/
def padEnterPath : List
    (Challenge.EvmProof.Stepper.Located referenceArtifact .Osaka) :=
  [⟨764, .push ⟨2, by decide⟩ (UInt256.ofNat 0x62c), by rfl, by decide⟩,
   ⟨765, .push ⟨0, by decide⟩ ⟨0⟩, by rfl, by decide⟩,
   ⟨766, .push ⟨2, by decide⟩ (UInt256.ofNat 0x1e0), by rfl, by decide⟩,
   ⟨767, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

/-- Cached located path for RIPEMD padded-length arithmetic. -/
def padLengthPath : List
    (Challenge.EvmProof.Stepper.Located referenceArtifact .Osaka) :=
  [⟨349, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨350, .op .CALLDATASIZE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨351, .push ⟨1, by decide⟩ (UInt256.ofNat 72), by rfl, by decide⟩,
   ⟨352, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨353, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨354, .push ⟨1, by decide⟩ (UInt256.ofNat 6), by rfl, by decide⟩,
   ⟨355, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨356, .push ⟨1, by decide⟩ (UInt256.ofNat 6), by rfl, by decide⟩,
   ⟨357, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨358, .op (.Swap ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨359, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩]

/-- Cached located path for copying calldata and setting up the footer loop. -/
def padSetupPath : List
    (Challenge.EvmProof.Stepper.Located referenceArtifact .Osaka) :=
  [⟨360, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨361, .push ⟨0, by decide⟩ ⟨0⟩, by rfl, by decide⟩,
   ⟨362, .push ⟨2, by decide⟩ (UInt256.ofNat 0x800), by rfl, by decide⟩,
   ⟨363, .op .CALLDATACOPY, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨364, .push ⟨1, by decide⟩ (UInt256.ofNat 128), by rfl, by decide⟩,
   ⟨365, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨366, .push ⟨2, by decide⟩ (UInt256.ofNat 0x800), by rfl, by decide⟩,
   ⟨367, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨368, .op .MSTORE8, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨369, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨370, .push ⟨1, by decide⟩ (UInt256.ofNat 3), by rfl, by decide⟩,
   ⟨371, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨372, .push ⟨1, by decide⟩ (UInt256.ofNat 8), by rfl, by decide⟩,
   ⟨373, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨374, .op .SUB, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨375, .push ⟨2, by decide⟩ (UInt256.ofNat 0x800), by rfl, by decide⟩,
   ⟨376, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨377, .push ⟨0, by decide⟩ ⟨0⟩, by rfl, by decide⟩,
   ⟨378, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩]


end Challenge.Ripemd160.Reference.Proofs.Bytecode.Artifact
