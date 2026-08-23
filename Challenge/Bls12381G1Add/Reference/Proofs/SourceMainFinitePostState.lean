import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainFinitePostDefs

set_option warningAsError true

/-! # G1ADD common post-slope state graph -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def mainFinitePostLambdaSqWords (st : EvmState) (lam : U256 × U256) :
    U256 × U256 := fpMulResult st lam.1 lam.2 lam.1 lam.2

def mainFinitePostState0 (st : EvmState) (lam : U256 × U256) : EvmState :=
  fpMulFinalState st lam.1 lam.2 lam.1 lam.2

def mainFinitePostX1ArgsState (st : EvmState) (lam : U256 × U256) :
    EvmState := afterTwoLoads (mainFinitePostState0 st lam) 0 32

def mainFinitePostX3FirstWords (yst : EvmState) (st : EvmState)
    (lam : U256 × U256) : U256 × U256 :=
  let sq := mainFinitePostLambdaSqWords st lam
  fpSubValue sq.1 sq.2 (mainDecodedWord yst 0) (mainDecodedWord yst 32)

def mainFinitePostX2ArgsState (_yst : EvmState) (st : EvmState)
    (lam : U256 × U256) : EvmState :=
  afterTwoLoads (mainFinitePostX1ArgsState st lam) 128 160

def mainFinitePostX3Words (yst : EvmState) (st : EvmState)
    (lam : U256 × U256) : U256 × U256 :=
  let first := mainFinitePostX3FirstWords yst st lam
  fpSubValue first.1 first.2
    (mainDecodedWord yst 128) (mainDecodedWord yst 160)

def mainFinitePostDeltaArgsState (yst : EvmState) (st : EvmState)
    (lam : U256 × U256) : EvmState :=
  afterTwoLoads (mainFinitePostX2ArgsState yst st lam) 0 32

def mainFinitePostDeltaWords (yst : EvmState) (st : EvmState)
    (lam : U256 × U256) : U256 × U256 :=
  let x3 := mainFinitePostX3Words yst st lam
  fpSubValue (mainDecodedWord yst 0) (mainDecodedWord yst 32) x3.1 x3.2

def mainFinitePostYProductWords (yst : EvmState) (st : EvmState)
    (lam : U256 × U256) : U256 × U256 :=
  let delta := mainFinitePostDeltaWords yst st lam
  fpMulResult (mainFinitePostDeltaArgsState yst st lam)
    lam.1 lam.2 delta.1 delta.2

def mainFinitePostState1 (yst : EvmState) (st : EvmState)
    (lam : U256 × U256) : EvmState :=
  let delta := mainFinitePostDeltaWords yst st lam
  fpMulFinalState (mainFinitePostDeltaArgsState yst st lam)
    lam.1 lam.2 delta.1 delta.2

def mainFinitePostY1ArgsState (yst : EvmState) (st : EvmState)
    (lam : U256 × U256) : EvmState :=
  afterTwoLoads (mainFinitePostState1 yst st lam) 64 96

def mainFinitePostY3Words (yst : EvmState) (st : EvmState)
    (lam : U256 × U256) : U256 × U256 :=
  let product := mainFinitePostYProductWords yst st lam
  fpSubValue product.1 product.2
    (mainDecodedWord yst 64) (mainDecodedWord yst 96)

def mainFinitePostStoredState (yst : EvmState) (st : EvmState)
    (lam : U256 × U256) : EvmState :=
  let x3 := mainFinitePostX3Words yst st lam
  let y3 := mainFinitePostY3Words yst st lam
  mainStorePointState (mainFinitePostY1ArgsState yst st lam)
    x3.1 x3.2 y3.1 y3.2

def mainFinitePostReturnState (yst : EvmState) (st : EvmState)
    (lam : U256 × U256) : EvmState :=
  let stored := mainFinitePostStoredState yst st lam
  { touchMemory stored 0 128 with
    halted := some (.ret, readBytes stored.memory 0 128) }

def mainFinitePostEnv0 (base : VEnv Challenge.EvmProof.modexpExec.toDialect)
    (st : EvmState) (lam : U256 × U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x00114", (mainFinitePostLambdaSqWords st lam).1),
    ("\x00115", (mainFinitePostLambdaSqWords st lam).2)] ++ base

def mainFinitePostEnv1 (yst : EvmState)
    (base : VEnv Challenge.EvmProof.modexpExec.toDialect)
    (st : EvmState) (lam : U256 × U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.setMany (mainFinitePostEnv0 base st lam) ["\x00114", "\x00115"]
    [(mainFinitePostX3FirstWords yst st lam).1,
      (mainFinitePostX3FirstWords yst st lam).2]

def mainFinitePostEnv2 (yst : EvmState)
    (base : VEnv Challenge.EvmProof.modexpExec.toDialect)
    (st : EvmState) (lam : U256 × U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.setMany (mainFinitePostEnv1 yst base st lam) ["\x00114", "\x00115"]
    [(mainFinitePostX3Words yst st lam).1,
      (mainFinitePostX3Words yst st lam).2]

def mainFinitePostEnv3 (yst : EvmState)
    (base : VEnv Challenge.EvmProof.modexpExec.toDialect)
    (st : EvmState) (lam : U256 × U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x00116", (mainFinitePostDeltaWords yst st lam).1),
    ("\x00117", (mainFinitePostDeltaWords yst st lam).2)] ++
      mainFinitePostEnv2 yst base st lam

def mainFinitePostEnv4 (yst : EvmState)
    (base : VEnv Challenge.EvmProof.modexpExec.toDialect)
    (st : EvmState) (lam : U256 × U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x00118", (mainFinitePostYProductWords yst st lam).1),
    ("\x00119", (mainFinitePostYProductWords yst st lam).2)] ++
      mainFinitePostEnv3 yst base st lam

def mainFinitePostEnv5 (yst : EvmState)
    (base : VEnv Challenge.EvmProof.modexpExec.toDialect)
    (st : EvmState) (lam : U256 × U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.setMany (mainFinitePostEnv4 yst base st lam) ["\x00118", "\x00119"]
    [(mainFinitePostY3Words yst st lam).1,
      (mainFinitePostY3Words yst st lam).2]

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
