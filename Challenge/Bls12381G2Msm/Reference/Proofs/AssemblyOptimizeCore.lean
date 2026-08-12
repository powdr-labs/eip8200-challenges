import Challenge.Bls12381G2Msm.Reference.Proofs.Compilation
import Challenge.Bls12381G2Msm.Reference.Proofs.FrozenAssembly

set_option warningAsError true

namespace Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

def assemblyChunksOf (size : Nat) : Nat → List α → List (List α)
  | 0, xs => [xs]
  | count + 1, xs => xs.take size :: assemblyChunksOf size count (xs.drop size)

theorem flatten_assemblyChunksOf (size count : Nat) (xs : List α) :
    (assemblyChunksOf size count xs).flatten = xs := by
  induction count generalizing xs with
  | zero => simp [assemblyChunksOf]
  | succ count ih =>
      simp only [assemblyChunksOf, List.flatten_cons, ih]
      exact List.take_append_drop size xs

def referenceComputedAssemblyChunks : List (List YulEvmCompiler.Asm) :=
  assemblyChunksOf 200 9 referenceComputedOptimizedAssembly

def referenceFrozenAssemblyChunks : List (List YulEvmCompiler.Asm) :=
  [ frozenReferenceAssemblyChunk0,
    frozenReferenceAssemblyChunk1,
    frozenReferenceAssemblyChunk2,
    frozenReferenceAssemblyChunk3,
    frozenReferenceAssemblyChunk4,
    frozenReferenceAssemblyChunk5,
    frozenReferenceAssemblyChunk6,
    frozenReferenceAssemblyChunk7,
    frozenReferenceAssemblyChunk8,
    frozenReferenceAssemblyChunk9 ]

theorem referenceComputedAssemblyChunks_flatten :
    referenceComputedAssemblyChunks.flatten =
      referenceComputedOptimizedAssembly :=
  flatten_assemblyChunksOf 200 9 referenceComputedOptimizedAssembly

set_option maxRecDepth 30000 in
theorem referenceFrozenAssemblyChunks_flatten :
    referenceFrozenAssemblyChunks.flatten = referenceOptimizedAssembly := by
  rfl

end Challenge.Bls12381G2Msm.Reference.Proofs.Compilation
