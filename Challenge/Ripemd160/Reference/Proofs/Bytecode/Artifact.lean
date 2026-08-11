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
  .push 2 27,
  op 0x56,
  op 0x5b,
  .push 4 4294967295,
  op 0x81,
  op 0x83,
  .push 1 32,
  op 0x03,
  op 0x1c,
  op 0x82,
  op 0x84,
  op 0x1b,
  op 0x17,
  op 0x16,
  op 0x92,
  op 0x50,
  op 0x50,
  op 0x50,
  op 0x90,
  op 0x56,
  op 0x5b,
  .push 2 46,
  op 0x56,
  op 0x5b,
  op 0x80,
  .push 1 5,
  op 0x1b,
  .push 1 32,
  op 0x01,
  op 0x51,
  op 0x91,
  op 0x50,
  op 0x50,
  op 0x90,
  op 0x56,
  op 0x5b,
  .push 2 70,
  op 0x56,
  op 0x5b,
  .push 4 4294967295,
  op 0x83,
  op 0x16,
  op 0x82,
  .push 1 5,
  op 0x1b,
  op 0x82,
  op 0x01,
  op 0x52,
  op 0x50,
  op 0x50,
  op 0x50,
  op 0x56,
  op 0x5b,
  .push 2 90,
  op 0x56,
  op 0x5b,
  op 0x80,
  .push 1 5,
  op 0x1b,
  .push 2 672,
  op 0x01,
  op 0x51,
  op 0x91,
  op 0x50,
  op 0x50,
  op 0x90,
  op 0x56,
  op 0x5b,
  .push 2 115,
  op 0x56,
  op 0x5b,
  .push 4 4294967295,
  op 0x82,
  op 0x16,
  op 0x81,
  .push 1 5,
  op 0x1b,
  .push 2 672,
  op 0x01,
  op 0x52,
  op 0x50,
  op 0x50,
  op 0x56,
  op 0x5b,
  .push 2 142,
  op 0x56,
  op 0x5b,
  op 0x81,
  .push 1 5,
  op 0x1c,
  .push 1 5,
  op 0x1b,
  op 0x81,
  op 0x01,
  op 0x51,
  .push 1 31,
  op 0x83,
  op 0x16,
  op 0x1a,
  op 0x92,
  op 0x50,
  op 0x50,
  op 0x50,
  op 0x90,
  op 0x56,
  op 0x5b,
  .push 2 271,
  op 0x56,
  op 0x5b,
  op 0x80,
  op 0x80,
  .push 0 0,
  op 0x14,
  op 0x15,
  .push 2 169,
  op 0x57,
  op 0x50,
  op 0x83,
  op 0x83,
  op 0x83,
  op 0x18,
  op 0x18,
  op 0x94,
  op 0x50,
  .push 2 264,
  op 0x56,
  op 0x5b,
  op 0x80,
  .push 1 1,
  op 0x14,
  op 0x15,
  .push 2 194,
  op 0x57,
  op 0x50,
  op 0x83,
  op 0x82,
  op 0x19,
  op 0x16,
  op 0x83,
  op 0x83,
  op 0x16,
  op 0x17,
  op 0x94,
  op 0x50,
  .push 2 264,
  op 0x56,
  op 0x5b,
  op 0x80,
  .push 1 2,
  op 0x14,
  op 0x15,
  .push 2 223,
  op 0x57,
  op 0x50,
  .push 4 4294967295,
  op 0x84,
  op 0x84,
  op 0x19,
  op 0x84,
  op 0x17,
  op 0x18,
  op 0x16,
  op 0x94,
  op 0x50,
  .push 2 264,
  op 0x56,
  op 0x5b,
  op 0x80,
  .push 1 3,
  op 0x14,
  op 0x15,
  .push 2 248,
  op 0x57,
  op 0x50,
  op 0x83,
  op 0x19,
  op 0x83,
  op 0x16,
  op 0x84,
  op 0x83,
  op 0x16,
  op 0x17,
  op 0x94,
  op 0x50,
  .push 2 264,
  op 0x56,
  op 0x5b,
  op 0x50,
  .push 4 4294967295,
  op 0x84,
  op 0x19,
  op 0x84,
  op 0x17,
  op 0x83,
  op 0x18,
  op 0x16,
  op 0x94,
  op 0x50,
  op 0x5b,
  op 0x50,
  op 0x50,
  op 0x50,
  op 0x50,
  op 0x90,
  op 0x56,
  op 0x5b,
  .push 2 434,
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
  .push 4 4294967295,
  op 0x8a,
  .push 2 314,
  .push 0 0,
  op 0x8b,
  .push 2 75,
  op 0x56,
  op 0x5b,
  .push 2 327,
  .push 0 0,
  op 0x86,
  op 0x88,
  op 0x8a,
  op 0x8e,
  .push 2 147,
  op 0x56,
  op 0x5b,
  op 0x88,
  op 0x01,
  op 0x01,
  op 0x01,
  op 0x16,
  .push 4 4294967295,
  op 0x82,
  .push 2 349,
  .push 0 0,
  op 0x8d,
  op 0x85,
  .push 2 4,
  op 0x56,
  op 0x5b,
  op 0x01,
  op 0x16,
  op 0x90,
  op 0x50,
  .push 4 4294967295,
  op 0x82,
  op 0x16,
  op 0x87,
  op 0x52,
  .push 4 4294967295,
  op 0x83,
  op 0x16,
  .push 1 128,
  op 0x88,
  op 0x01,
  op 0x52,
  .push 2 397,
  .push 2 389,
  .push 0 0,
  .push 1 10,
  op 0x87,
  .push 2 4,
  op 0x56,
  op 0x5b,
  .push 1 3,
  op 0x89,
  .push 2 51,
  op 0x56,
  op 0x5b,
  .push 4 4294967295,
  op 0x85,
  op 0x16,
  .push 1 64,
  op 0x88,
  op 0x01,
  op 0x52,
  .push 4 4294967295,
  op 0x81,
  op 0x16,
  .push 1 32,
  op 0x88,
  op 0x01,
  op 0x52,
  op 0x50,
  op 0x50,
  op 0x50,
  op 0x50,
  op 0x50,
  op 0x50,
  op 0x50,
  op 0x50,
  op 0x50,
  op 0x50,
  op 0x50,
  op 0x56,
  op 0x5b,
  .push 2 475,
  op 0x56,
  op 0x5b,
  op 0x80,
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
  op 0x82,
  .push 0 0,
  op 0x1a,
  op 0x17,
  op 0x17,
  op 0x92,
  op 0x50,
  op 0x50,
  op 0x50,
  op 0x90,
  op 0x56,
  op 0x5b,
  .push 2 561,
  op 0x56,
  op 0x5b,
  op 0x36,
  .push 1 72,
  op 0x81,
  op 0x01,
  .push 1 6,
  op 0x1c,
  .push 1 6,
  op 0x1b,
  op 0x91,
  op 0x50,
  op 0x80,
  .push 0 0,
  .push 2 2048,
  op 0x37,
  .push 1 128,
  op 0x81,
  .push 2 2048,
  op 0x01,
  op 0x53,
  op 0x80,
  .push 1 3,
  op 0x1b,
  .push 1 8,
  op 0x83,
  op 0x03,
  .push 2 2048,
  op 0x01,
  .push 0 0,
  op 0x5b,
  .push 1 8,
  op 0x81,
  op 0x10,
  op 0x15,
  .push 2 554,
  op 0x57,
  .push 1 255,
  op 0x83,
  op 0x82,
  .push 1 3,
  op 0x1b,
  op 0x1c,
  op 0x16,
  op 0x81,
  op 0x83,
  op 0x01,
  op 0x53,
  .push 1 1,
  op 0x81,
  op 0x01,
  op 0x90,
  op 0x50,
  .push 2 521,
  op 0x56,
  op 0x5b,
  op 0x50,
  op 0x50,
  op 0x50,
  op 0x50,
  op 0x90,
  op 0x56,
  op 0x5b,
  .push 2 616,
  op 0x56,
  op 0x5b,
  .push 0 0,
  op 0x5b,
  .push 1 16,
  op 0x81,
  op 0x10,
  op 0x15,
  .push 2 612,
  op 0x57,
  .push 2 601,
  .push 2 595,
  .push 0 0,
  op 0x83,
  .push 1 2,
  op 0x1b,
  op 0x85,
  op 0x01,
  .push 2 439,
  op 0x56,
  op 0x5b,
  op 0x82,
  .push 2 95,
  op 0x56,
  op 0x5b,
  .push 1 1,
  op 0x81,
  op 0x01,
  op 0x90,
  op 0x50,
  .push 2 568,
  op 0x56,
  op 0x5b,
  op 0x50,
  op 0x50,
  op 0x56,
  op 0x5b,
  .push 2 961,
  op 0x56,
  op 0x5b,
  .push 2 630,
  op 0x81,
  .push 2 566,
  op 0x56,
  op 0x5b,
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
  op 0x5b,
  .push 1 80,
  op 0x81,
  op 0x10,
  op 0x15,
  .push 2 726,
  op 0x57,
  op 0x80,
  .push 1 4,
  op 0x1c,
  .push 2 714,
  op 0x81,
  .push 1 5,
  op 0x1b,
  .push 2 1568,
  op 0x01,
  op 0x51,
  .push 2 693,
  .push 0 0,
  op 0x85,
  .push 2 1376,
  .push 2 120,
  op 0x56,
  op 0x5b,
  .push 2 706,
  .push 0 0,
  op 0x86,
  .push 2 1184,
  .push 2 120,
  op 0x56,
  op 0x5b,
  op 0x84,
  .push 1 192,
  .push 2 276,
  op 0x56,
  op 0x5b,
  op 0x50,
  .push 1 1,
  op 0x81,
  op 0x01,
  op 0x90,
  op 0x50,
  .push 2 655,
  op 0x56,
  op 0x5b,
  op 0x50,
  .push 0 0,
  op 0x5b,
  .push 1 80,
  op 0x81,
  op 0x10,
  op 0x15,
  .push 2 804,
  op 0x57,
  op 0x80,
  .push 1 4,
  op 0x1c,
  .push 2 792,
  op 0x81,
  .push 1 5,
  op 0x1b,
  .push 2 1728,
  op 0x01,
  op 0x51,
  .push 2 767,
  .push 0 0,
  op 0x85,
  .push 2 1472,
  .push 2 120,
  op 0x56,
  op 0x5b,
  .push 2 780,
  .push 0 0,
  op 0x86,
  .push 2 1280,
  .push 2 120,
  op 0x56,
  op 0x5b,
  op 0x84,
  .push 1 4,
  op 0x03,
  .push 2 352,
  .push 2 276,
  op 0x56,
  op 0x5b,
  op 0x50,
  .push 1 1,
  op 0x81,
  op 0x01,
  op 0x90,
  op 0x50,
  .push 2 729,
  op 0x56,
  op 0x5b,
  op 0x50,
  .push 4 4294967295,
  .push 2 448,
  op 0x51,
  .push 2 256,
  op 0x51,
  .push 2 544,
  op 0x51,
  op 0x01,
  op 0x01,
  op 0x16,
  .push 4 4294967295,
  .push 2 480,
  op 0x51,
  .push 2 288,
  op 0x51,
  .push 2 576,
  op 0x51,
  op 0x01,
  op 0x01,
  op 0x16,
  .push 4 4294967295,
  op 0x81,
  op 0x16,
  .push 1 64,
  op 0x52,
  .push 4 4294967295,
  .push 2 352,
  op 0x51,
  .push 2 320,
  op 0x51,
  .push 2 608,
  op 0x51,
  op 0x01,
  op 0x01,
  op 0x16,
  .push 4 4294967295,
  op 0x81,
  op 0x16,
  .push 1 96,
  op 0x52,
  .push 4 4294967295,
  .push 2 384,
  op 0x51,
  .push 1 192,
  op 0x51,
  .push 2 640,
  op 0x51,
  op 0x01,
  op 0x01,
  op 0x16,
  .push 4 4294967295,
  op 0x81,
  op 0x16,
  .push 1 128,
  op 0x52,
  .push 4 4294967295,
  .push 2 416,
  op 0x51,
  .push 1 224,
  op 0x51,
  .push 2 512,
  op 0x51,
  op 0x01,
  op 0x01,
  op 0x16,
  .push 4 4294967295,
  op 0x81,
  op 0x16,
  .push 1 160,
  op 0x52,
  .push 4 4294967295,
  op 0x85,
  op 0x16,
  .push 1 32,
  op 0x52,
  op 0x50,
  op 0x50,
  op 0x50,
  op 0x50,
  op 0x50,
  op 0x50,
  op 0x56,
  op 0x5b,
  .push 2 1006,
  op 0x56,
  op 0x5b,
  .push 0 0,
  op 0x5b,
  .push 1 4,
  op 0x81,
  op 0x10,
  op 0x15,
  .push 2 1001,
  op 0x57,
  .push 1 255,
  op 0x83,
  op 0x82,
  .push 1 3,
  op 0x1b,
  op 0x1c,
  op 0x16,
  op 0x81,
  op 0x83,
  op 0x01,
  op 0x53,
  .push 1 1,
  op 0x81,
  op 0x01,
  op 0x90,
  op 0x50,
  .push 2 968,
  op 0x56,
  op 0x5b,
  op 0x50,
  op 0x50,
  op 0x50,
  op 0x56,
  op 0x5b,
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
  .push 2 1580,
  .push 0 0,
  .push 2 480,
  op 0x56,
  op 0x5b,
  .push 0 0,
  op 0x5b,
  op 0x81,
  op 0x81,
  op 0x10,
  op 0x15,
  .push 2 1614,
  op 0x57,
  .push 2 1603,
  op 0x81,
  .push 2 2048,
  op 0x01,
  .push 2 621,
  op 0x56,
  op 0x5b,
  .push 1 64,
  op 0x81,
  op 0x01,
  op 0x90,
  op 0x50,
  .push 2 1582,
  op 0x56,
  op 0x5b,
  op 0x50,
  .push 0 0,
  .push 0 0,
  op 0x52,
  .push 0 0,
  op 0x5b,
  .push 1 5,
  op 0x81,
  op 0x10,
  op 0x15,
  .push 2 1665,
  op 0x57,
  .push 2 1654,
  .push 2 1642,
  .push 0 0,
  op 0x83,
  .push 2 32,
  op 0x56,
  op 0x5b,
  op 0x82,
  .push 1 2,
  op 0x1b,
  .push 1 12,
  op 0x01,
  .push 2 966,
  op 0x56,
  op 0x5b,
  .push 1 1,
  op 0x81,
  op 0x01,
  op 0x90,
  op 0x50,
  .push 2 1620,
  op 0x56,
  op 0x5b,
  op 0x50,
  .push 1 32,
  .push 0 0,
  op 0xf3
]

theorem referenceInstructions_count : referenceInstructions.length = 831 := by
  decide

theorem assemble_referenceInstructions :
    assemble referenceInstructions = referenceBytecode := by
  native_decide

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
  [⟨683, 31, 1780731860627700044960722568376592188711674974810043212252563479055960840, 2, 1184⟩,
   ⟨686, 32, 1374703749640218873849524064026661036561295975619335768036000015621818746370, 2, 1216⟩,
   ⟨689, 32, 1809286146446445343010337679715913357291520642540487409382712519614204477440, 2, 1248⟩,
   ⟨692, 32, 2286348414996307935469207465186628553155355030353023797310855598864584999170, 2, 1280⟩,
   ⟨695, 32, 6793533947442029545286681365244130742947859423983440781638017424580845963790, 2, 1312⟩,
   ⟨698, 32, 5454326014381509071620663843103927214778145566039445656282506490595801825280, 2, 1344⟩,
   ⟨701, 32, 5000281043567253289773844389228683908720941172611121566642559091978571025676, 2, 1376⟩,
   ⟨704, 32, 4998451946933852135137276647445154408072640462072745561656555001729660617996, 2, 1408⟩,
   ⟨707, 32, 4097353149147406276549177442451244923784709130172834976461593227075946283008, 2, 1440⟩,
   ⟨710, 32, 3634466825900925589093651101374881051901026410458987220032629834781140389131, 2, 1472⟩,
   ⟨713, 32, 4083287390302437702768465126624575726298108573653391417181074648310269415176, 2, 1504⟩,
   ⟨716, 32, 3627420088851531435467691758328083203359072412578514691593700216701345333248, 2, 1536⟩,
   ⟨719, 0, 0, 2, 1568⟩,
   ⟨722, 4, 1518500249, 2, 1600⟩,
   ⟨725, 4, 1859775393, 2, 1632⟩,
   ⟨728, 4, 2400959708, 2, 1664⟩,
   ⟨731, 4, 2840853838, 2, 1696⟩,
   ⟨734, 4, 1352829926, 2, 1728⟩,
   ⟨737, 4, 1548603684, 2, 1760⟩,
   ⟨740, 4, 1836072691, 2, 1792⟩,
   ⟨743, 4, 2053994217, 2, 1824⟩,
   ⟨746, 0, 0, 2, 1856⟩,
   ⟨749, 4, 1732584193, 1, 32⟩,
   ⟨752, 4, 4023233417, 1, 64⟩,
   ⟨755, 4, 2562383102, 1, 96⟩,
   ⟨758, 4, 271733878, 1, 128⟩,
   ⟨761, 4, 3285377520, 1, 160⟩]

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
    referenceArtifact.instructionPC 683 = 0x3ef := by rfl

@[simp] theorem referenceArtifact_pc_684 :
    referenceArtifact.instructionPC 684 = 0x40f := by rfl

@[simp] theorem referenceArtifact_pc_685 :
    referenceArtifact.instructionPC 685 = 0x412 := by rfl

@[simp] theorem referenceArtifact_pc_686 :
    referenceArtifact.instructionPC 686 = 0x413 := by rfl

@[simp] theorem referenceArtifact_pc_687 :
    referenceArtifact.instructionPC 687 = 0x434 := by rfl

@[simp] theorem referenceArtifact_pc_688 :
    referenceArtifact.instructionPC 688 = 0x437 := by rfl

@[simp] theorem referenceArtifact_pc_689 :
    referenceArtifact.instructionPC 689 = 0x438 := by rfl

@[simp] theorem referenceArtifact_pc_690 :
    referenceArtifact.instructionPC 690 = 0x459 := by rfl

@[simp] theorem referenceArtifact_pc_691 :
    referenceArtifact.instructionPC 691 = 0x45c := by rfl

@[simp] theorem referenceArtifact_pc_692 :
    referenceArtifact.instructionPC 692 = 0x45d := by rfl

@[simp] theorem referenceArtifact_pc_693 :
    referenceArtifact.instructionPC 693 = 0x47e := by rfl

@[simp] theorem referenceArtifact_pc_694 :
    referenceArtifact.instructionPC 694 = 0x481 := by rfl

@[simp] theorem referenceArtifact_pc_695 :
    referenceArtifact.instructionPC 695 = 0x482 := by rfl

@[simp] theorem referenceArtifact_pc_696 :
    referenceArtifact.instructionPC 696 = 0x4a3 := by rfl

@[simp] theorem referenceArtifact_pc_697 :
    referenceArtifact.instructionPC 697 = 0x4a6 := by rfl

@[simp] theorem referenceArtifact_pc_698 :
    referenceArtifact.instructionPC 698 = 0x4a7 := by rfl

@[simp] theorem referenceArtifact_pc_699 :
    referenceArtifact.instructionPC 699 = 0x4c8 := by rfl

@[simp] theorem referenceArtifact_pc_700 :
    referenceArtifact.instructionPC 700 = 0x4cb := by rfl

@[simp] theorem referenceArtifact_pc_701 :
    referenceArtifact.instructionPC 701 = 0x4cc := by rfl

@[simp] theorem referenceArtifact_pc_702 :
    referenceArtifact.instructionPC 702 = 0x4ed := by rfl

@[simp] theorem referenceArtifact_pc_703 :
    referenceArtifact.instructionPC 703 = 0x4f0 := by rfl

@[simp] theorem referenceArtifact_pc_704 :
    referenceArtifact.instructionPC 704 = 0x4f1 := by rfl

@[simp] theorem referenceArtifact_pc_705 :
    referenceArtifact.instructionPC 705 = 0x512 := by rfl

@[simp] theorem referenceArtifact_pc_706 :
    referenceArtifact.instructionPC 706 = 0x515 := by rfl

@[simp] theorem referenceArtifact_pc_707 :
    referenceArtifact.instructionPC 707 = 0x516 := by rfl

@[simp] theorem referenceArtifact_pc_708 :
    referenceArtifact.instructionPC 708 = 0x537 := by rfl

@[simp] theorem referenceArtifact_pc_709 :
    referenceArtifact.instructionPC 709 = 0x53a := by rfl

@[simp] theorem referenceArtifact_pc_710 :
    referenceArtifact.instructionPC 710 = 0x53b := by rfl

@[simp] theorem referenceArtifact_pc_711 :
    referenceArtifact.instructionPC 711 = 0x55c := by rfl

@[simp] theorem referenceArtifact_pc_712 :
    referenceArtifact.instructionPC 712 = 0x55f := by rfl

@[simp] theorem referenceArtifact_pc_713 :
    referenceArtifact.instructionPC 713 = 0x560 := by rfl

@[simp] theorem referenceArtifact_pc_714 :
    referenceArtifact.instructionPC 714 = 0x581 := by rfl

@[simp] theorem referenceArtifact_pc_715 :
    referenceArtifact.instructionPC 715 = 0x584 := by rfl

@[simp] theorem referenceArtifact_pc_716 :
    referenceArtifact.instructionPC 716 = 0x585 := by rfl

@[simp] theorem referenceArtifact_pc_717 :
    referenceArtifact.instructionPC 717 = 0x5a6 := by rfl

@[simp] theorem referenceArtifact_pc_718 :
    referenceArtifact.instructionPC 718 = 0x5a9 := by rfl

@[simp] theorem referenceArtifact_pc_719 :
    referenceArtifact.instructionPC 719 = 0x5aa := by rfl

@[simp] theorem referenceArtifact_pc_720 :
    referenceArtifact.instructionPC 720 = 0x5ab := by rfl

@[simp] theorem referenceArtifact_pc_721 :
    referenceArtifact.instructionPC 721 = 0x5ae := by rfl

@[simp] theorem referenceArtifact_pc_722 :
    referenceArtifact.instructionPC 722 = 0x5af := by rfl

@[simp] theorem referenceArtifact_pc_723 :
    referenceArtifact.instructionPC 723 = 0x5b4 := by rfl

@[simp] theorem referenceArtifact_pc_724 :
    referenceArtifact.instructionPC 724 = 0x5b7 := by rfl

@[simp] theorem referenceArtifact_pc_725 :
    referenceArtifact.instructionPC 725 = 0x5b8 := by rfl

@[simp] theorem referenceArtifact_pc_726 :
    referenceArtifact.instructionPC 726 = 0x5bd := by rfl

@[simp] theorem referenceArtifact_pc_727 :
    referenceArtifact.instructionPC 727 = 0x5c0 := by rfl

@[simp] theorem referenceArtifact_pc_728 :
    referenceArtifact.instructionPC 728 = 0x5c1 := by rfl

@[simp] theorem referenceArtifact_pc_729 :
    referenceArtifact.instructionPC 729 = 0x5c6 := by rfl

@[simp] theorem referenceArtifact_pc_730 :
    referenceArtifact.instructionPC 730 = 0x5c9 := by rfl

@[simp] theorem referenceArtifact_pc_731 :
    referenceArtifact.instructionPC 731 = 0x5ca := by rfl

@[simp] theorem referenceArtifact_pc_732 :
    referenceArtifact.instructionPC 732 = 0x5cf := by rfl

@[simp] theorem referenceArtifact_pc_733 :
    referenceArtifact.instructionPC 733 = 0x5d2 := by rfl

@[simp] theorem referenceArtifact_pc_734 :
    referenceArtifact.instructionPC 734 = 0x5d3 := by rfl

@[simp] theorem referenceArtifact_pc_735 :
    referenceArtifact.instructionPC 735 = 0x5d8 := by rfl

@[simp] theorem referenceArtifact_pc_736 :
    referenceArtifact.instructionPC 736 = 0x5db := by rfl

@[simp] theorem referenceArtifact_pc_737 :
    referenceArtifact.instructionPC 737 = 0x5dc := by rfl

@[simp] theorem referenceArtifact_pc_738 :
    referenceArtifact.instructionPC 738 = 0x5e1 := by rfl

@[simp] theorem referenceArtifact_pc_739 :
    referenceArtifact.instructionPC 739 = 0x5e4 := by rfl

@[simp] theorem referenceArtifact_pc_740 :
    referenceArtifact.instructionPC 740 = 0x5e5 := by rfl

@[simp] theorem referenceArtifact_pc_741 :
    referenceArtifact.instructionPC 741 = 0x5ea := by rfl

@[simp] theorem referenceArtifact_pc_742 :
    referenceArtifact.instructionPC 742 = 0x5ed := by rfl

@[simp] theorem referenceArtifact_pc_743 :
    referenceArtifact.instructionPC 743 = 0x5ee := by rfl

@[simp] theorem referenceArtifact_pc_744 :
    referenceArtifact.instructionPC 744 = 0x5f3 := by rfl

@[simp] theorem referenceArtifact_pc_745 :
    referenceArtifact.instructionPC 745 = 0x5f6 := by rfl

@[simp] theorem referenceArtifact_pc_746 :
    referenceArtifact.instructionPC 746 = 0x5f7 := by rfl

@[simp] theorem referenceArtifact_pc_747 :
    referenceArtifact.instructionPC 747 = 0x5f8 := by rfl

@[simp] theorem referenceArtifact_pc_748 :
    referenceArtifact.instructionPC 748 = 0x5fb := by rfl

@[simp] theorem referenceArtifact_pc_749 :
    referenceArtifact.instructionPC 749 = 0x5fc := by rfl

@[simp] theorem referenceArtifact_pc_750 :
    referenceArtifact.instructionPC 750 = 0x601 := by rfl

@[simp] theorem referenceArtifact_pc_751 :
    referenceArtifact.instructionPC 751 = 0x603 := by rfl

@[simp] theorem referenceArtifact_pc_752 :
    referenceArtifact.instructionPC 752 = 0x604 := by rfl

@[simp] theorem referenceArtifact_pc_753 :
    referenceArtifact.instructionPC 753 = 0x609 := by rfl

@[simp] theorem referenceArtifact_pc_754 :
    referenceArtifact.instructionPC 754 = 0x60b := by rfl

@[simp] theorem referenceArtifact_pc_755 :
    referenceArtifact.instructionPC 755 = 0x60c := by rfl

@[simp] theorem referenceArtifact_pc_756 :
    referenceArtifact.instructionPC 756 = 0x611 := by rfl

@[simp] theorem referenceArtifact_pc_757 :
    referenceArtifact.instructionPC 757 = 0x613 := by rfl

@[simp] theorem referenceArtifact_pc_758 :
    referenceArtifact.instructionPC 758 = 0x614 := by rfl

@[simp] theorem referenceArtifact_pc_759 :
    referenceArtifact.instructionPC 759 = 0x619 := by rfl

@[simp] theorem referenceArtifact_pc_760 :
    referenceArtifact.instructionPC 760 = 0x61b := by rfl

@[simp] theorem referenceArtifact_pc_761 :
    referenceArtifact.instructionPC 761 = 0x61c := by rfl

@[simp] theorem referenceArtifact_pc_762 :
    referenceArtifact.instructionPC 762 = 0x621 := by rfl

@[simp] theorem referenceArtifact_pc_763 :
    referenceArtifact.instructionPC 763 = 0x623 := by rfl


@[simp] theorem referenceArtifact_pc_764 :
    referenceArtifact.instructionPC 764 = 0x624 := by rfl

@[simp] theorem referenceArtifact_pc_765 :
    referenceArtifact.instructionPC 765 = 0x627 := by rfl

@[simp] theorem referenceArtifact_pc_766 :
    referenceArtifact.instructionPC 766 = 0x628 := by rfl

@[simp] theorem referenceArtifact_pc_767 :
    referenceArtifact.instructionPC 767 = 0x62b := by rfl

@[simp] theorem referenceArtifact_pc_0 :
    referenceArtifact.instructionPC 0 = 0x0 := by rfl

@[simp] theorem referenceArtifact_pc_1 :
    referenceArtifact.instructionPC 1 = 0x3 := by rfl

@[simp] theorem referenceArtifact_pc_20 :
    referenceArtifact.instructionPC 20 = 0x1b := by rfl

@[simp] theorem referenceArtifact_pc_21 :
    referenceArtifact.instructionPC 21 = 0x1c := by rfl

@[simp] theorem referenceArtifact_pc_22 :
    referenceArtifact.instructionPC 22 = 0x1f := by rfl

@[simp] theorem referenceArtifact_pc_35 :
    referenceArtifact.instructionPC 35 = 0x2e := by rfl

@[simp] theorem referenceArtifact_pc_36 :
    referenceArtifact.instructionPC 36 = 0x2f := by rfl

@[simp] theorem referenceArtifact_pc_37 :
    referenceArtifact.instructionPC 37 = 0x32 := by rfl

@[simp] theorem referenceArtifact_pc_52 :
    referenceArtifact.instructionPC 52 = 0x46 := by rfl

@[simp] theorem referenceArtifact_pc_53 :
    referenceArtifact.instructionPC 53 = 0x47 := by rfl

@[simp] theorem referenceArtifact_pc_54 :
    referenceArtifact.instructionPC 54 = 0x4a := by rfl

@[simp] theorem referenceArtifact_pc_67 :
    referenceArtifact.instructionPC 67 = 0x5a := by rfl

@[simp] theorem referenceArtifact_pc_68 :
    referenceArtifact.instructionPC 68 = 0x5b := by rfl

@[simp] theorem referenceArtifact_pc_69 :
    referenceArtifact.instructionPC 69 = 0x5e := by rfl

@[simp] theorem referenceArtifact_pc_83 :
    referenceArtifact.instructionPC 83 = 0x73 := by rfl

@[simp] theorem referenceArtifact_pc_84 :
    referenceArtifact.instructionPC 84 = 0x74 := by rfl

@[simp] theorem referenceArtifact_pc_85 :
    referenceArtifact.instructionPC 85 = 0x77 := by rfl

@[simp] theorem referenceArtifact_pc_105 :
    referenceArtifact.instructionPC 105 = 0x8e := by rfl

@[simp] theorem referenceArtifact_pc_106 :
    referenceArtifact.instructionPC 106 = 0x8f := by rfl

@[simp] theorem referenceArtifact_pc_107 :
    referenceArtifact.instructionPC 107 = 0x92 := by rfl

@[simp] theorem referenceArtifact_pc_205 :
    referenceArtifact.instructionPC 205 = 0x10f := by rfl

@[simp] theorem referenceArtifact_pc_206 :
    referenceArtifact.instructionPC 206 = 0x110 := by rfl

@[simp] theorem referenceArtifact_pc_207 :
    referenceArtifact.instructionPC 207 = 0x113 := by rfl

@[simp] theorem referenceArtifact_pc_313 :
    referenceArtifact.instructionPC 313 = 0x1b2 := by rfl

@[simp] theorem referenceArtifact_pc_314 :
    referenceArtifact.instructionPC 314 = 0x1b3 := by rfl

@[simp] theorem referenceArtifact_pc_315 :
    referenceArtifact.instructionPC 315 = 0x1b6 := by rfl

@[simp] theorem referenceArtifact_pc_346 :
    referenceArtifact.instructionPC 346 = 0x1db := by rfl

@[simp] theorem referenceArtifact_pc_347 :
    referenceArtifact.instructionPC 347 = 0x1dc := by rfl

@[simp] theorem referenceArtifact_pc_348 :
    referenceArtifact.instructionPC 348 = 0x1df := by rfl

@[simp] theorem referenceArtifact_pc_410 :
    referenceArtifact.instructionPC 410 = 0x231 := by rfl

@[simp] theorem referenceArtifact_pc_411 :
    referenceArtifact.instructionPC 411 = 0x232 := by rfl

@[simp] theorem referenceArtifact_pc_412 :
    referenceArtifact.instructionPC 412 = 0x235 := by rfl

@[simp] theorem referenceArtifact_pc_448 :
    referenceArtifact.instructionPC 448 = 0x268 := by rfl

@[simp] theorem referenceArtifact_pc_449 :
    referenceArtifact.instructionPC 449 = 0x269 := by rfl

@[simp] theorem referenceArtifact_pc_450 :
    referenceArtifact.instructionPC 450 = 0x26c := by rfl

@[simp] theorem referenceArtifact_pc_647 :
    referenceArtifact.instructionPC 647 = 0x3c1 := by rfl

@[simp] theorem referenceArtifact_pc_648 :
    referenceArtifact.instructionPC 648 = 0x3c2 := by rfl

@[simp] theorem referenceArtifact_pc_649 :
    referenceArtifact.instructionPC 649 = 0x3c5 := by rfl

@[simp] theorem referenceArtifact_pc_682 :
    referenceArtifact.instructionPC 682 = 0x3ee := by rfl

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
    referenceArtifact.instructionPC 349 = 0x1e0 := by rfl
@[simp] theorem pc349 :
    instructionPC 349 = 0x1e0 := by rfl

@[simp] theorem refPc350 :
    referenceArtifact.instructionPC 350 = 0x1e1 := by rfl
@[simp] theorem pc350 :
    instructionPC 350 = 0x1e1 := by rfl

@[simp] theorem refPc351 :
    referenceArtifact.instructionPC 351 = 0x1e2 := by rfl
@[simp] theorem pc351 :
    instructionPC 351 = 0x1e2 := by rfl

@[simp] theorem refPc352 :
    referenceArtifact.instructionPC 352 = 0x1e4 := by rfl
@[simp] theorem pc352 :
    instructionPC 352 = 0x1e4 := by rfl

@[simp] theorem refPc353 :
    referenceArtifact.instructionPC 353 = 0x1e5 := by rfl
@[simp] theorem pc353 :
    instructionPC 353 = 0x1e5 := by rfl

@[simp] theorem refPc354 :
    referenceArtifact.instructionPC 354 = 0x1e6 := by rfl
@[simp] theorem pc354 :
    instructionPC 354 = 0x1e6 := by rfl

@[simp] theorem refPc355 :
    referenceArtifact.instructionPC 355 = 0x1e8 := by rfl
@[simp] theorem pc355 :
    instructionPC 355 = 0x1e8 := by rfl

@[simp] theorem refPc356 :
    referenceArtifact.instructionPC 356 = 0x1e9 := by rfl
@[simp] theorem pc356 :
    instructionPC 356 = 0x1e9 := by rfl

@[simp] theorem refPc357 :
    referenceArtifact.instructionPC 357 = 0x1eb := by rfl
@[simp] theorem pc357 :
    instructionPC 357 = 0x1eb := by rfl

@[simp] theorem refPc358 :
    referenceArtifact.instructionPC 358 = 0x1ec := by rfl
@[simp] theorem pc358 :
    instructionPC 358 = 0x1ec := by rfl

@[simp] theorem refPc359 :
    referenceArtifact.instructionPC 359 = 0x1ed := by rfl
@[simp] theorem pc359 :
    instructionPC 359 = 0x1ed := by rfl

@[simp] theorem refPc360 :
    referenceArtifact.instructionPC 360 = 0x1ee := by rfl
@[simp] theorem pc360 :
    instructionPC 360 = 0x1ee := by rfl

@[simp] theorem refPc361 :
    referenceArtifact.instructionPC 361 = 0x1ef := by rfl
@[simp] theorem pc361 :
    instructionPC 361 = 0x1ef := by rfl

@[simp] theorem refPc362 :
    referenceArtifact.instructionPC 362 = 0x1f0 := by rfl
@[simp] theorem pc362 :
    instructionPC 362 = 0x1f0 := by rfl

@[simp] theorem refPc363 :
    referenceArtifact.instructionPC 363 = 0x1f3 := by rfl
@[simp] theorem pc363 :
    instructionPC 363 = 0x1f3 := by rfl

@[simp] theorem refPc364 :
    referenceArtifact.instructionPC 364 = 0x1f4 := by rfl
@[simp] theorem pc364 :
    instructionPC 364 = 0x1f4 := by rfl

@[simp] theorem refPc365 :
    referenceArtifact.instructionPC 365 = 0x1f6 := by rfl
@[simp] theorem pc365 :
    instructionPC 365 = 0x1f6 := by rfl

@[simp] theorem refPc366 :
    referenceArtifact.instructionPC 366 = 0x1f7 := by rfl
@[simp] theorem pc366 :
    instructionPC 366 = 0x1f7 := by rfl

@[simp] theorem refPc367 :
    referenceArtifact.instructionPC 367 = 0x1fa := by rfl
@[simp] theorem pc367 :
    instructionPC 367 = 0x1fa := by rfl

@[simp] theorem refPc368 :
    referenceArtifact.instructionPC 368 = 0x1fb := by rfl
@[simp] theorem pc368 :
    instructionPC 368 = 0x1fb := by rfl

@[simp] theorem refPc369 :
    referenceArtifact.instructionPC 369 = 0x1fc := by rfl
@[simp] theorem pc369 :
    instructionPC 369 = 0x1fc := by rfl

@[simp] theorem refPc370 :
    referenceArtifact.instructionPC 370 = 0x1fd := by rfl
@[simp] theorem pc370 :
    instructionPC 370 = 0x1fd := by rfl

@[simp] theorem refPc371 :
    referenceArtifact.instructionPC 371 = 0x1ff := by rfl
@[simp] theorem pc371 :
    instructionPC 371 = 0x1ff := by rfl

@[simp] theorem refPc372 :
    referenceArtifact.instructionPC 372 = 0x200 := by rfl
@[simp] theorem pc372 :
    instructionPC 372 = 0x200 := by rfl

@[simp] theorem refPc373 :
    referenceArtifact.instructionPC 373 = 0x202 := by rfl
@[simp] theorem pc373 :
    instructionPC 373 = 0x202 := by rfl

@[simp] theorem refPc374 :
    referenceArtifact.instructionPC 374 = 0x203 := by rfl
@[simp] theorem pc374 :
    instructionPC 374 = 0x203 := by rfl

@[simp] theorem refPc375 :
    referenceArtifact.instructionPC 375 = 0x204 := by rfl
@[simp] theorem pc375 :
    instructionPC 375 = 0x204 := by rfl

@[simp] theorem refPc376 :
    referenceArtifact.instructionPC 376 = 0x207 := by rfl
@[simp] theorem pc376 :
    instructionPC 376 = 0x207 := by rfl

@[simp] theorem refPc377 :
    referenceArtifact.instructionPC 377 = 0x208 := by rfl
@[simp] theorem pc377 :
    instructionPC 377 = 0x208 := by rfl

@[simp] theorem refPc378 :
    referenceArtifact.instructionPC 378 = 0x209 := by rfl
@[simp] theorem pc378 :
    instructionPC 378 = 0x209 := by rfl

@[simp] theorem refPc379 :
    referenceArtifact.instructionPC 379 = 0x20a := by rfl
@[simp] theorem pc379 :
    instructionPC 379 = 0x20a := by rfl

@[simp] theorem refPc380 :
    referenceArtifact.instructionPC 380 = 0x20c := by rfl
@[simp] theorem pc380 :
    instructionPC 380 = 0x20c := by rfl

@[simp] theorem refPc381 :
    referenceArtifact.instructionPC 381 = 0x20d := by rfl
@[simp] theorem pc381 :
    instructionPC 381 = 0x20d := by rfl

@[simp] theorem refPc382 :
    referenceArtifact.instructionPC 382 = 0x20e := by rfl
@[simp] theorem pc382 :
    instructionPC 382 = 0x20e := by rfl

@[simp] theorem refPc383 :
    referenceArtifact.instructionPC 383 = 0x20f := by rfl
@[simp] theorem pc383 :
    instructionPC 383 = 0x20f := by rfl

@[simp] theorem refPc384 :
    referenceArtifact.instructionPC 384 = 0x212 := by rfl
@[simp] theorem pc384 :
    instructionPC 384 = 0x212 := by rfl

@[simp] theorem refPc385 :
    referenceArtifact.instructionPC 385 = 0x213 := by rfl
@[simp] theorem pc385 :
    instructionPC 385 = 0x213 := by rfl

@[simp] theorem refPc386 :
    referenceArtifact.instructionPC 386 = 0x215 := by rfl
@[simp] theorem pc386 :
    instructionPC 386 = 0x215 := by rfl

@[simp] theorem refPc387 :
    referenceArtifact.instructionPC 387 = 0x216 := by rfl
@[simp] theorem pc387 :
    instructionPC 387 = 0x216 := by rfl

@[simp] theorem refPc388 :
    referenceArtifact.instructionPC 388 = 0x217 := by rfl
@[simp] theorem pc388 :
    instructionPC 388 = 0x217 := by rfl

@[simp] theorem refPc389 :
    referenceArtifact.instructionPC 389 = 0x219 := by rfl
@[simp] theorem pc389 :
    instructionPC 389 = 0x219 := by rfl

@[simp] theorem refPc390 :
    referenceArtifact.instructionPC 390 = 0x21a := by rfl
@[simp] theorem pc390 :
    instructionPC 390 = 0x21a := by rfl

@[simp] theorem refPc391 :
    referenceArtifact.instructionPC 391 = 0x21b := by rfl
@[simp] theorem pc391 :
    instructionPC 391 = 0x21b := by rfl

@[simp] theorem refPc392 :
    referenceArtifact.instructionPC 392 = 0x21c := by rfl
@[simp] theorem pc392 :
    instructionPC 392 = 0x21c := by rfl

@[simp] theorem refPc393 :
    referenceArtifact.instructionPC 393 = 0x21d := by rfl
@[simp] theorem pc393 :
    instructionPC 393 = 0x21d := by rfl

@[simp] theorem refPc394 :
    referenceArtifact.instructionPC 394 = 0x21e := by rfl
@[simp] theorem pc394 :
    instructionPC 394 = 0x21e := by rfl

@[simp] theorem refPc395 :
    referenceArtifact.instructionPC 395 = 0x21f := by rfl
@[simp] theorem pc395 :
    instructionPC 395 = 0x21f := by rfl

@[simp] theorem refPc396 :
    referenceArtifact.instructionPC 396 = 0x220 := by rfl
@[simp] theorem pc396 :
    instructionPC 396 = 0x220 := by rfl

@[simp] theorem refPc397 :
    referenceArtifact.instructionPC 397 = 0x222 := by rfl
@[simp] theorem pc397 :
    instructionPC 397 = 0x222 := by rfl

@[simp] theorem refPc398 :
    referenceArtifact.instructionPC 398 = 0x223 := by rfl
@[simp] theorem pc398 :
    instructionPC 398 = 0x223 := by rfl

@[simp] theorem refPc399 :
    referenceArtifact.instructionPC 399 = 0x224 := by rfl
@[simp] theorem pc399 :
    instructionPC 399 = 0x224 := by rfl

@[simp] theorem refPc400 :
    referenceArtifact.instructionPC 400 = 0x225 := by rfl
@[simp] theorem pc400 :
    instructionPC 400 = 0x225 := by rfl

@[simp] theorem refPc401 :
    referenceArtifact.instructionPC 401 = 0x226 := by rfl
@[simp] theorem pc401 :
    instructionPC 401 = 0x226 := by rfl

@[simp] theorem refPc402 :
    referenceArtifact.instructionPC 402 = 0x229 := by rfl
@[simp] theorem pc402 :
    instructionPC 402 = 0x229 := by rfl

@[simp] theorem refPc403 :
    referenceArtifact.instructionPC 403 = 0x22a := by rfl
@[simp] theorem pc403 :
    instructionPC 403 = 0x22a := by rfl

@[simp] theorem refPc404 :
    referenceArtifact.instructionPC 404 = 0x22b := by rfl
@[simp] theorem pc404 :
    instructionPC 404 = 0x22b := by rfl

@[simp] theorem refPc405 :
    referenceArtifact.instructionPC 405 = 0x22c := by rfl
@[simp] theorem pc405 :
    instructionPC 405 = 0x22c := by rfl

@[simp] theorem refPc406 :
    referenceArtifact.instructionPC 406 = 0x22d := by rfl
@[simp] theorem pc406 :
    instructionPC 406 = 0x22d := by rfl

@[simp] theorem refPc407 :
    referenceArtifact.instructionPC 407 = 0x22e := by rfl
@[simp] theorem pc407 :
    instructionPC 407 = 0x22e := by rfl

@[simp] theorem refPc408 :
    referenceArtifact.instructionPC 408 = 0x22f := by rfl
@[simp] theorem pc408 :
    instructionPC 408 = 0x22f := by rfl

@[simp] theorem refPc409 :
    referenceArtifact.instructionPC 409 = 0x230 := by rfl
@[simp] theorem pc409 :
    instructionPC 409 = 0x230 := by rfl

private theorem wfOp {op : Operation}
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
