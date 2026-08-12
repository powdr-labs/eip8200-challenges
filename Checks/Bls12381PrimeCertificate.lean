import Challenge.Bls12381.ProofSupport.PrimeCertificate

set_option warningAsError true

namespace Checks.Bls12381PrimeCertificate

open Challenge.Bls12381.ProofSupport.PrimeCertificate

#print axioms prime3373
#print axioms prime1453
#print axioms prime1327
#print axioms prime2741
#print axioms prime7577
#print axioms prime582767
#print axioms prime8101
#print axioms prime1151
#print axioms prime1686913
#print axioms prime16447
#print axioms prime43591
#print axioms prime927093389
#print axioms prime51376543
#print axioms prime755057
#print axioms prime421987
#print axioms prime47737
#print axioms prime609743
#print axioms prime10177
#print axioms prime859267
#print axioms prime52437899
#print axioms prime9272813673901
#print axioms prime1928745244171409
#print axioms prime13090036741
#print axioms prime64881703735777
#print axioms prime43670061551
#print axioms prime3819663927398918131021
#print axioms prime7259797099061183477
#print axioms prime475709467
#print axioms prime92691255082156974996979
#print axioms prime1125266252156850182658904441386709967
#print axioms prime2584487767265781317813
#print axioms prime15778400344354997994418419698270088123916926905054652752758194827714659
#print axioms prime_certifiedModulus
#print axioms prime_p
#print axioms lawful_mul_inv_cancel_p

example (a : Challenge.Bls12381.ProofSupport.PrimeField.LawfulFp) (ha : a ≠ 0) :
    a * a⁻¹ = 1 := lawful_mul_inv_cancel_p a ha

end Checks.Bls12381PrimeCertificate
