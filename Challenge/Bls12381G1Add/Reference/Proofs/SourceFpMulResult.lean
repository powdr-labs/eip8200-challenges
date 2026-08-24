import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpMulBody

set_option warningAsError true
set_option maxHeartbeats 100000

/-! # Opaque native `fpMul` result components -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

theorem fpMulResultValue_hi_graph (ahi alo bhi blo : U256) :
    (fpMulResultValue ahi alo bhi blo).1 =
      (fpMulResultGraph ahi alo bhi blo).hi :=
  congrArg Prod.fst (fpMulResultValue_spec ahi alo bhi blo)

theorem fpMulResultValue_lo_graph (ahi alo bhi blo : U256) :
    (fpMulResultValue ahi alo bhi blo).2 =
      (fpMulResultGraph ahi alo bhi blo).lo :=
  congrArg Prod.snd (fpMulResultValue_spec ahi alo bhi blo)

theorem fpMulResult_hi_graph (yst : EvmState) (ahi alo bhi blo : U256) :
    (fpMulResult yst ahi alo bhi blo).1 =
      (fpMulResultGraph ahi alo bhi blo).hi :=
  fpMulResultValue_hi_graph ahi alo bhi blo

theorem fpMulResult_lo_graph (yst : EvmState) (ahi alo bhi blo : U256) :
    (fpMulResult yst ahi alo bhi blo).2 =
      (fpMulResultGraph ahi alo bhi blo).lo :=
  fpMulResultValue_lo_graph ahi alo bhi blo

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
