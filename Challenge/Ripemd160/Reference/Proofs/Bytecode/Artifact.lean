import Challenge.EvmProof.Stepper
import Challenge.Ripemd160.Reference.Bytecode
set_option warningAsError true
set_option maxRecDepth 100000
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

/-! ### Instruction-PC table

Generated from the instruction list for the indices the re-derived proofs
anchor on.  The old table's index set described the old layout and none of it
survived the re-schedule.  A *complete* table is not an option here: each entry
is an `rfl` that folds the instruction list up to its index, so 847 of them cost
more than ten minutes of elaboration.

The local `instructionPC` abbreviation gets one reduction lemma rather than a
second table; it is definitionally the artifact's own projection. -/

@[simp] theorem instructionPC_eq (index : Nat) :
    instructionPC index = referenceArtifact.instructionPC index := rfl


@[simp] theorem referenceArtifact_pc_0 :
    referenceArtifact.instructionPC 0 = 0x0 := by rfl

@[simp] theorem referenceArtifact_pc_1 :
    referenceArtifact.instructionPC 1 = 0x20 := by rfl

@[simp] theorem referenceArtifact_pc_2 :
    referenceArtifact.instructionPC 2 = 0x23 := by rfl

@[simp] theorem referenceArtifact_pc_3 :
    referenceArtifact.instructionPC 3 = 0x24 := by rfl

@[simp] theorem referenceArtifact_pc_4 :
    referenceArtifact.instructionPC 4 = 0x45 := by rfl

@[simp] theorem referenceArtifact_pc_5 :
    referenceArtifact.instructionPC 5 = 0x48 := by rfl

@[simp] theorem referenceArtifact_pc_6 :
    referenceArtifact.instructionPC 6 = 0x49 := by rfl

@[simp] theorem referenceArtifact_pc_7 :
    referenceArtifact.instructionPC 7 = 0x6a := by rfl

@[simp] theorem referenceArtifact_pc_8 :
    referenceArtifact.instructionPC 8 = 0x6d := by rfl

@[simp] theorem referenceArtifact_pc_9 :
    referenceArtifact.instructionPC 9 = 0x6e := by rfl

@[simp] theorem referenceArtifact_pc_10 :
    referenceArtifact.instructionPC 10 = 0x8f := by rfl

@[simp] theorem referenceArtifact_pc_11 :
    referenceArtifact.instructionPC 11 = 0x92 := by rfl

@[simp] theorem referenceArtifact_pc_12 :
    referenceArtifact.instructionPC 12 = 0x93 := by rfl

@[simp] theorem referenceArtifact_pc_13 :
    referenceArtifact.instructionPC 13 = 0xb4 := by rfl

@[simp] theorem referenceArtifact_pc_14 :
    referenceArtifact.instructionPC 14 = 0xb7 := by rfl

@[simp] theorem referenceArtifact_pc_15 :
    referenceArtifact.instructionPC 15 = 0xb8 := by rfl

@[simp] theorem referenceArtifact_pc_16 :
    referenceArtifact.instructionPC 16 = 0xd9 := by rfl

@[simp] theorem referenceArtifact_pc_17 :
    referenceArtifact.instructionPC 17 = 0xdc := by rfl

@[simp] theorem referenceArtifact_pc_18 :
    referenceArtifact.instructionPC 18 = 0xdd := by rfl

@[simp] theorem referenceArtifact_pc_19 :
    referenceArtifact.instructionPC 19 = 0xfe := by rfl

@[simp] theorem referenceArtifact_pc_20 :
    referenceArtifact.instructionPC 20 = 0x101 := by rfl

@[simp] theorem referenceArtifact_pc_21 :
    referenceArtifact.instructionPC 21 = 0x102 := by rfl

@[simp] theorem referenceArtifact_pc_22 :
    referenceArtifact.instructionPC 22 = 0x123 := by rfl

@[simp] theorem referenceArtifact_pc_23 :
    referenceArtifact.instructionPC 23 = 0x126 := by rfl

@[simp] theorem referenceArtifact_pc_24 :
    referenceArtifact.instructionPC 24 = 0x127 := by rfl

@[simp] theorem referenceArtifact_pc_25 :
    referenceArtifact.instructionPC 25 = 0x148 := by rfl

@[simp] theorem referenceArtifact_pc_26 :
    referenceArtifact.instructionPC 26 = 0x14b := by rfl

@[simp] theorem referenceArtifact_pc_27 :
    referenceArtifact.instructionPC 27 = 0x14c := by rfl

@[simp] theorem referenceArtifact_pc_28 :
    referenceArtifact.instructionPC 28 = 0x16d := by rfl

@[simp] theorem referenceArtifact_pc_29 :
    referenceArtifact.instructionPC 29 = 0x170 := by rfl

@[simp] theorem referenceArtifact_pc_30 :
    referenceArtifact.instructionPC 30 = 0x171 := by rfl

@[simp] theorem referenceArtifact_pc_31 :
    referenceArtifact.instructionPC 31 = 0x192 := by rfl

@[simp] theorem referenceArtifact_pc_32 :
    referenceArtifact.instructionPC 32 = 0x195 := by rfl

@[simp] theorem referenceArtifact_pc_33 :
    referenceArtifact.instructionPC 33 = 0x196 := by rfl

@[simp] theorem referenceArtifact_pc_34 :
    referenceArtifact.instructionPC 34 = 0x1b7 := by rfl

@[simp] theorem referenceArtifact_pc_35 :
    referenceArtifact.instructionPC 35 = 0x1ba := by rfl

@[simp] theorem referenceArtifact_pc_36 :
    referenceArtifact.instructionPC 36 = 0x1bb := by rfl

@[simp] theorem referenceArtifact_pc_37 :
    referenceArtifact.instructionPC 37 = 0x1bc := by rfl

@[simp] theorem referenceArtifact_pc_38 :
    referenceArtifact.instructionPC 38 = 0x1bf := by rfl

@[simp] theorem referenceArtifact_pc_39 :
    referenceArtifact.instructionPC 39 = 0x1c0 := by rfl

@[simp] theorem referenceArtifact_pc_40 :
    referenceArtifact.instructionPC 40 = 0x1c5 := by rfl

@[simp] theorem referenceArtifact_pc_41 :
    referenceArtifact.instructionPC 41 = 0x1c8 := by rfl

@[simp] theorem referenceArtifact_pc_42 :
    referenceArtifact.instructionPC 42 = 0x1c9 := by rfl

@[simp] theorem referenceArtifact_pc_43 :
    referenceArtifact.instructionPC 43 = 0x1ce := by rfl

@[simp] theorem referenceArtifact_pc_44 :
    referenceArtifact.instructionPC 44 = 0x1d1 := by rfl

@[simp] theorem referenceArtifact_pc_45 :
    referenceArtifact.instructionPC 45 = 0x1d2 := by rfl

@[simp] theorem referenceArtifact_pc_46 :
    referenceArtifact.instructionPC 46 = 0x1d7 := by rfl

@[simp] theorem referenceArtifact_pc_47 :
    referenceArtifact.instructionPC 47 = 0x1da := by rfl

@[simp] theorem referenceArtifact_pc_48 :
    referenceArtifact.instructionPC 48 = 0x1db := by rfl

@[simp] theorem referenceArtifact_pc_49 :
    referenceArtifact.instructionPC 49 = 0x1e0 := by rfl

@[simp] theorem referenceArtifact_pc_50 :
    referenceArtifact.instructionPC 50 = 0x1e3 := by rfl

@[simp] theorem referenceArtifact_pc_51 :
    referenceArtifact.instructionPC 51 = 0x1e4 := by rfl

@[simp] theorem referenceArtifact_pc_52 :
    referenceArtifact.instructionPC 52 = 0x1e9 := by rfl

@[simp] theorem referenceArtifact_pc_53 :
    referenceArtifact.instructionPC 53 = 0x1ec := by rfl

@[simp] theorem referenceArtifact_pc_54 :
    referenceArtifact.instructionPC 54 = 0x1ed := by rfl

@[simp] theorem referenceArtifact_pc_55 :
    referenceArtifact.instructionPC 55 = 0x1f2 := by rfl

@[simp] theorem referenceArtifact_pc_56 :
    referenceArtifact.instructionPC 56 = 0x1f5 := by rfl

@[simp] theorem referenceArtifact_pc_57 :
    referenceArtifact.instructionPC 57 = 0x1f6 := by rfl

@[simp] theorem referenceArtifact_pc_58 :
    referenceArtifact.instructionPC 58 = 0x1fb := by rfl

@[simp] theorem referenceArtifact_pc_59 :
    referenceArtifact.instructionPC 59 = 0x1fe := by rfl

@[simp] theorem referenceArtifact_pc_60 :
    referenceArtifact.instructionPC 60 = 0x1ff := by rfl

@[simp] theorem referenceArtifact_pc_61 :
    referenceArtifact.instructionPC 61 = 0x204 := by rfl

@[simp] theorem referenceArtifact_pc_62 :
    referenceArtifact.instructionPC 62 = 0x207 := by rfl

@[simp] theorem referenceArtifact_pc_63 :
    referenceArtifact.instructionPC 63 = 0x208 := by rfl

@[simp] theorem referenceArtifact_pc_64 :
    referenceArtifact.instructionPC 64 = 0x209 := by rfl

@[simp] theorem referenceArtifact_pc_65 :
    referenceArtifact.instructionPC 65 = 0x20c := by rfl

@[simp] theorem referenceArtifact_pc_66 :
    referenceArtifact.instructionPC 66 = 0x20d := by rfl

@[simp] theorem referenceArtifact_pc_67 :
    referenceArtifact.instructionPC 67 = 0x212 := by rfl

@[simp] theorem referenceArtifact_pc_68 :
    referenceArtifact.instructionPC 68 = 0x214 := by rfl

@[simp] theorem referenceArtifact_pc_69 :
    referenceArtifact.instructionPC 69 = 0x215 := by rfl

@[simp] theorem referenceArtifact_pc_70 :
    referenceArtifact.instructionPC 70 = 0x21a := by rfl

@[simp] theorem referenceArtifact_pc_71 :
    referenceArtifact.instructionPC 71 = 0x21c := by rfl

@[simp] theorem referenceArtifact_pc_72 :
    referenceArtifact.instructionPC 72 = 0x21d := by rfl

@[simp] theorem referenceArtifact_pc_73 :
    referenceArtifact.instructionPC 73 = 0x222 := by rfl

@[simp] theorem referenceArtifact_pc_74 :
    referenceArtifact.instructionPC 74 = 0x224 := by rfl

@[simp] theorem referenceArtifact_pc_75 :
    referenceArtifact.instructionPC 75 = 0x225 := by rfl

@[simp] theorem referenceArtifact_pc_76 :
    referenceArtifact.instructionPC 76 = 0x22a := by rfl

@[simp] theorem referenceArtifact_pc_77 :
    referenceArtifact.instructionPC 77 = 0x22c := by rfl

@[simp] theorem referenceArtifact_pc_78 :
    referenceArtifact.instructionPC 78 = 0x22d := by rfl

@[simp] theorem referenceArtifact_pc_79 :
    referenceArtifact.instructionPC 79 = 0x232 := by rfl

@[simp] theorem referenceArtifact_pc_80 :
    referenceArtifact.instructionPC 80 = 0x234 := by rfl

@[simp] theorem referenceArtifact_pc_81 :
    referenceArtifact.instructionPC 81 = 0x235 := by rfl

@[simp] theorem referenceArtifact_pc_82 :
    referenceArtifact.instructionPC 82 = 0x236 := by rfl

@[simp] theorem referenceArtifact_pc_83 :
    referenceArtifact.instructionPC 83 = 0x238 := by rfl

@[simp] theorem referenceArtifact_pc_84 :
    referenceArtifact.instructionPC 84 = 0x239 := by rfl

@[simp] theorem referenceArtifact_pc_85 :
    referenceArtifact.instructionPC 85 = 0x23a := by rfl

@[simp] theorem referenceArtifact_pc_86 :
    referenceArtifact.instructionPC 86 = 0x23c := by rfl

@[simp] theorem referenceArtifact_pc_87 :
    referenceArtifact.instructionPC 87 = 0x23d := by rfl

@[simp] theorem referenceArtifact_pc_88 :
    referenceArtifact.instructionPC 88 = 0x23f := by rfl

@[simp] theorem referenceArtifact_pc_89 :
    referenceArtifact.instructionPC 89 = 0x240 := by rfl

@[simp] theorem referenceArtifact_pc_90 :
    referenceArtifact.instructionPC 90 = 0x241 := by rfl

@[simp] theorem referenceArtifact_pc_91 :
    referenceArtifact.instructionPC 91 = 0x244 := by rfl

@[simp] theorem referenceArtifact_pc_92 :
    referenceArtifact.instructionPC 92 = 0x245 := by rfl

@[simp] theorem referenceArtifact_pc_93 :
    referenceArtifact.instructionPC 93 = 0x246 := by rfl

@[simp] theorem referenceArtifact_pc_94 :
    referenceArtifact.instructionPC 94 = 0x247 := by rfl

@[simp] theorem referenceArtifact_pc_95 :
    referenceArtifact.instructionPC 95 = 0x248 := by rfl

@[simp] theorem referenceArtifact_pc_96 :
    referenceArtifact.instructionPC 96 = 0x24a := by rfl

@[simp] theorem referenceArtifact_pc_97 :
    referenceArtifact.instructionPC 97 = 0x24d := by rfl

@[simp] theorem referenceArtifact_pc_98 :
    referenceArtifact.instructionPC 98 = 0x24e := by rfl

@[simp] theorem referenceArtifact_pc_99 :
    referenceArtifact.instructionPC 99 = 0x24f := by rfl

@[simp] theorem referenceArtifact_pc_100 :
    referenceArtifact.instructionPC 100 = 0x250 := by rfl

@[simp] theorem referenceArtifact_pc_101 :
    referenceArtifact.instructionPC 101 = 0x252 := by rfl

@[simp] theorem referenceArtifact_pc_102 :
    referenceArtifact.instructionPC 102 = 0x253 := by rfl

@[simp] theorem referenceArtifact_pc_103 :
    referenceArtifact.instructionPC 103 = 0x254 := by rfl

@[simp] theorem referenceArtifact_pc_104 :
    referenceArtifact.instructionPC 104 = 0x255 := by rfl

@[simp] theorem referenceArtifact_pc_105 :
    referenceArtifact.instructionPC 105 = 0x256 := by rfl

@[simp] theorem referenceArtifact_pc_106 :
    referenceArtifact.instructionPC 106 = 0x258 := by rfl

@[simp] theorem referenceArtifact_pc_107 :
    referenceArtifact.instructionPC 107 = 0x259 := by rfl

@[simp] theorem referenceArtifact_pc_108 :
    referenceArtifact.instructionPC 108 = 0x25a := by rfl

@[simp] theorem referenceArtifact_pc_109 :
    referenceArtifact.instructionPC 109 = 0x25d := by rfl

@[simp] theorem referenceArtifact_pc_110 :
    referenceArtifact.instructionPC 110 = 0x25e := by rfl

@[simp] theorem referenceArtifact_pc_111 :
    referenceArtifact.instructionPC 111 = 0x25f := by rfl

@[simp] theorem referenceArtifact_pc_112 :
    referenceArtifact.instructionPC 112 = 0x262 := by rfl

@[simp] theorem referenceArtifact_pc_113 :
    referenceArtifact.instructionPC 113 = 0x263 := by rfl

@[simp] theorem referenceArtifact_pc_114 :
    referenceArtifact.instructionPC 114 = 0x264 := by rfl

@[simp] theorem referenceArtifact_pc_115 :
    referenceArtifact.instructionPC 115 = 0x265 := by rfl

@[simp] theorem referenceArtifact_pc_116 :
    referenceArtifact.instructionPC 116 = 0x266 := by rfl

@[simp] theorem referenceArtifact_pc_117 :
    referenceArtifact.instructionPC 117 = 0x267 := by rfl

@[simp] theorem referenceArtifact_pc_118 :
    referenceArtifact.instructionPC 118 = 0x26a := by rfl

@[simp] theorem referenceArtifact_pc_119 :
    referenceArtifact.instructionPC 119 = 0x26b := by rfl

@[simp] theorem referenceArtifact_pc_120 :
    referenceArtifact.instructionPC 120 = 0x26c := by rfl

@[simp] theorem referenceArtifact_pc_121 :
    referenceArtifact.instructionPC 121 = 0x26d := by rfl

@[simp] theorem referenceArtifact_pc_122 :
    referenceArtifact.instructionPC 122 = 0x26e := by rfl

@[simp] theorem referenceArtifact_pc_123 :
    referenceArtifact.instructionPC 123 = 0x26f := by rfl

@[simp] theorem referenceArtifact_pc_124 :
    referenceArtifact.instructionPC 124 = 0x270 := by rfl

@[simp] theorem referenceArtifact_pc_125 :
    referenceArtifact.instructionPC 125 = 0x271 := by rfl

@[simp] theorem referenceArtifact_pc_126 :
    referenceArtifact.instructionPC 126 = 0x274 := by rfl

@[simp] theorem referenceArtifact_pc_127 :
    referenceArtifact.instructionPC 127 = 0x275 := by rfl

@[simp] theorem referenceArtifact_pc_128 :
    referenceArtifact.instructionPC 128 = 0x276 := by rfl

@[simp] theorem referenceArtifact_pc_129 :
    referenceArtifact.instructionPC 129 = 0x279 := by rfl

@[simp] theorem referenceArtifact_pc_130 :
    referenceArtifact.instructionPC 130 = 0x27a := by rfl

@[simp] theorem referenceArtifact_pc_846 :
    referenceArtifact.instructionPC 846 = 0x699 := by rfl

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

/-! ### Padding paths

The new backend inlines `pad` into the program entry: initialization runs
straight into the padded-length arithmetic with an empty stack, so there is no
call sequence, no return address, and no output slot.  The old `padEnterPath`
(`PUSH2 0x62c; PUSH0; PUSH2 0x1e0; JUMP`) has no counterpart and is gone; the
two remaining paths start where initialization ends, at instruction 81. -/

/-- Cached located path for RIPEMD padded-length arithmetic.  Runs on the empty
stack left by initialization and leaves `[paddedWord, calldatasize]`. -/
def padLengthPath : List
    (Challenge.EvmProof.Stepper.Located referenceArtifact .Osaka) :=
  [⟨81, .op .CALLDATASIZE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨82, .push ⟨1, by decide⟩ (UInt256.ofNat 72), by rfl, by decide⟩,
   ⟨83, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨84, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨85, .push ⟨1, by decide⟩ (UInt256.ofNat 6), by rfl, by decide⟩,
   ⟨86, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨87, .push ⟨1, by decide⟩ (UInt256.ofNat 6), by rfl, by decide⟩,
   ⟨88, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩]

/-- Cached located path for copying calldata, writing the `0x80` sentinel, and
entering the footer loop.  Unlike the old layout this path ends with the jump to
the loop *condition* at `0x2b6`; the backend no longer falls through into a
`JUMPDEST`. -/
def padSetupPath : List
    (Challenge.EvmProof.Stepper.Located referenceArtifact .Osaka) :=
  [⟨89, .push ⟨0, by decide⟩ ⟨0⟩, by rfl, by decide⟩,
   ⟨90, .push ⟨2, by decide⟩ (UInt256.ofNat 0x800), by rfl, by decide⟩,
   ⟨91, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨92, .op (.Swap ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨93, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨94, .op .CALLDATACOPY, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨95, .push ⟨1, by decide⟩ (UInt256.ofNat 128), by rfl, by decide⟩,
   ⟨96, .push ⟨2, by decide⟩ (UInt256.ofNat 0x800), by rfl, by decide⟩,
   ⟨97, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨98, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨99, .op .MSTORE8, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨100, .push ⟨1, by decide⟩ (UInt256.ofNat 3), by rfl, by decide⟩,
   ⟨101, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨102, .op (.Swap ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨103, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨104, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨105, .push ⟨1, by decide⟩ (UInt256.ofNat 8), by rfl, by decide⟩,
   ⟨106, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨107, .op .SUB, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨108, .push ⟨2, by decide⟩ (UInt256.ofNat 0x800), by rfl, by decide⟩,
   ⟨109, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨110, .push ⟨0, by decide⟩ ⟨0⟩, by rfl, by decide⟩,
   ⟨111, .push ⟨2, by decide⟩ (UInt256.ofNat 0x2b6), by rfl, by decide⟩,
   ⟨112, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]


end Challenge.Ripemd160.Reference.Proofs.Bytecode.Artifact
