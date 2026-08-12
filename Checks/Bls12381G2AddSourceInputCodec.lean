import Challenge.Bls12381G2Add.Reference.Proofs.SourceInputCodec

open Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

#check decodeFp_eq_some_sourceField
#check decodeFp2_eq_some_sourceFp2
#check pointPaddingZero_iff_codec

#print axioms decodeFp2_eq_some_sourceFp2
#print axioms pointPaddingZero_iff_codec
