import Challenge.Bls12381G2Add.Reference.Proofs.SourcePointStoresExec

set_option warningAsError true

/-! # Frozen G2ADD main decode and validation definitions -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def mainFuns : FunEnv Challenge.EvmProof.modexpExec.toDialect := fp2Funs

def mainLengthStmt : Stmt Op := Compilation.referenceCompiledBlock[25]!

def mainStore0 : Stmt Op := Compilation.referenceCompiledBlock[26]!
def mainStore1 : Stmt Op := Compilation.referenceCompiledBlock[27]!
def mainStore2 : Stmt Op := Compilation.referenceCompiledBlock[28]!
def mainStore3 : Stmt Op := Compilation.referenceCompiledBlock[29]!
def mainStore4 : Stmt Op := Compilation.referenceCompiledBlock[30]!
def mainStore5 : Stmt Op := Compilation.referenceCompiledBlock[31]!
def mainStore6 : Stmt Op := Compilation.referenceCompiledBlock[32]!
def mainStore7 : Stmt Op := Compilation.referenceCompiledBlock[33]!
def mainStore8 : Stmt Op := Compilation.referenceCompiledBlock[34]!
def mainStore9 : Stmt Op := Compilation.referenceCompiledBlock[35]!
def mainStore10 : Stmt Op := Compilation.referenceCompiledBlock[36]!
def mainStore11 : Stmt Op := Compilation.referenceCompiledBlock[37]!
def mainStore12 : Stmt Op := Compilation.referenceCompiledBlock[38]!
def mainStore13 : Stmt Op := Compilation.referenceCompiledBlock[39]!
def mainStore14 : Stmt Op := Compilation.referenceCompiledBlock[40]!
def mainStore15 : Stmt Op := Compilation.referenceCompiledBlock[41]!

def mainStores : List (Stmt Op) :=
  [mainStore0, mainStore1, mainStore2, mainStore3,
    mainStore4, mainStore5, mainStore6, mainStore7,
    mainStore8, mainStore9, mainStore10, mainStore11,
    mainStore12, mainStore13, mainStore14, mainStore15]

def mainValidationStmt : Stmt Op := Compilation.referenceCompiledBlock[42]!
def mainPointScope : Stmt Op := Compilation.referenceCompiledBlock[43]!

def mainPointScopeBody : Block Op :=
  match mainPointScope with
  | .block body => body
  | _ => []

def mainInputWord (yst : EvmState) (offset : Nat) : U256 :=
  wordFrom yst.env.calldata offset

private def mainStoreWord (yst : EvmState) (offset : Nat) : EvmState :=
  { touchMemory yst offset 32 with
    memory := storeWord yst.memory offset (mainInputWord yst offset) }

def mainDecodedState4 (yst : EvmState) : EvmState :=
  let s0 := mainStoreWord yst 0
  let s1 := mainStoreWord s0 32
  let s2 := mainStoreWord s1 64
  mainStoreWord s2 96

def mainDecodedState8 (yst : EvmState) : EvmState :=
  let s4 := mainStoreWord (mainDecodedState4 yst) 128
  let s5 := mainStoreWord s4 160
  let s6 := mainStoreWord s5 192
  mainStoreWord s6 224

def mainDecodedState12 (yst : EvmState) : EvmState :=
  let s8 := mainStoreWord (mainDecodedState8 yst) 256
  let s9 := mainStoreWord s8 288
  let s10 := mainStoreWord s9 320
  mainStoreWord s10 352

def mainDecodedState (yst : EvmState) : EvmState :=
  let s12 := mainStoreWord (mainDecodedState12 yst) 384
  let s13 := mainStoreWord s12 416
  let s14 := mainStoreWord s13 448
  mainStoreWord s14 480

theorem mainDecodedState4_memory (yst : EvmState) :
    (mainDecodedState4 yst).memory =
      storeWord
        (storeWord
          (storeWord
            (storeWord yst.memory 0 (mainInputWord yst 0))
            32 (mainInputWord yst 32))
          64 (mainInputWord yst 64))
        96 (mainInputWord yst 96) := by
  rfl

theorem mainDecodedState8_memory (yst : EvmState) :
    (mainDecodedState8 yst).memory =
      storeWord
        (storeWord
          (storeWord
            (storeWord (mainDecodedState4 yst).memory 128 (mainInputWord yst 128))
            160 (mainInputWord yst 160))
          192 (mainInputWord yst 192))
        224 (mainInputWord yst 224) := by
  rfl

theorem mainDecodedState12_memory (yst : EvmState) :
    (mainDecodedState12 yst).memory =
      storeWord
        (storeWord
          (storeWord
            (storeWord (mainDecodedState8 yst).memory 256 (mainInputWord yst 256))
            288 (mainInputWord yst 288))
          320 (mainInputWord yst 320))
        352 (mainInputWord yst 352) := by
  rfl

theorem mainDecodedState_memory (yst : EvmState) :
    (mainDecodedState yst).memory =
      storeWord
        (storeWord
          (storeWord
            (storeWord (mainDecodedState12 yst).memory 384 (mainInputWord yst 384))
            416 (mainInputWord yst 416))
          448 (mainInputWord yst 448))
        480 (mainInputWord yst 480) := by
  rfl

def mainDecodedWord (yst : EvmState) (offset : Nat) : U256 :=
  loadWord (mainDecodedState yst).memory offset

def mainPoint2Valid (yst : EvmState) : U256 :=
  pointValidValue (mainDecodedState yst) 256

def mainAfterPoint2Valid (yst : EvmState) : EvmState :=
  pointValidReadState (mainDecodedState yst) 256

def mainPoint1Valid (yst : EvmState) : U256 :=
  pointValidValue (mainAfterPoint2Valid yst) 0

def mainAfterValidationReads (yst : EvmState) : EvmState :=
  pointValidReadState (mainAfterPoint2Valid yst) 0

def mainValidationValue (yst : EvmState) : U256 :=
  mainPoint1Valid yst &&& mainPoint2Valid yst

def mainInvalidState (yst : EvmState) : EvmState :=
  { yst with halted := some (.invalid, []) }

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
