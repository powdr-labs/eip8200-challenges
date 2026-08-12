import Challenge.EvmProof
import Challenge.EvmProof.StackCertificate
import Checks.EvmProofByteWindow
import Checks.EvmProofCallMemory
import Checks.EvmProofExecSound
import Checks.EvmProofModexpCallGas
import Checks.EvmProofModexpCalls
import Checks.EvmProofModexpExec
import Checks.EvmProofModexpMemory
import Checks.EvmProofModexpOne
import Checks.EvmProofProfiledCorrectness
import Checks.EvmProofProfiledCalls
import Checks.EvmProofProfiledLower
import Checks.EvmProofProfiledSteps
import Checks.EvmProofWideMul
set_option warningAsError true
/-!
# Shared EVM proof checks

Each `#guard_msgs in #print axioms …` pins the exact axiom set of a theorem.
If a `sorry` (which appears as `sorryAx`), a `native_decide`
(`Lean.ofReduceBool`), or any new axiom slips in, elaboration fails.
-/

/-- info: 'Challenge.EvmProof.Bytecode.assemble_disassemble' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.Bytecode.assemble_disassemble

/-- info: 'Challenge.EvmProof.Bytecode.JumpDestCertificate.valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.Bytecode.JumpDestCertificate.valid

/-- info: 'Challenge.EvmProof.eval_of_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.eval_of_steps

/-- info: 'Challenge.EvmProof.Reaches.toEval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.Reaches.toEval

/-- info: 'Challenge.EvmProof.Limbs.join_splitTwo' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Challenge.EvmProof.Limbs.join_splitTwo

/-- info: 'Challenge.EvmProof.MemoryRegion.disjoint_symm' does not depend on any axioms -/
#guard_msgs in
#print axioms Challenge.EvmProof.MemoryRegion.disjoint_symm

example {α : Type} (f : α → Bool) (xs : List α) (n : Nat)
    (hhead : (xs.take n).all f = true)
    (htail : (xs.drop n).all f = true) : xs.all f = true :=
  Challenge.EvmProof.StackCertificate.all_take_drop
    f xs n hhead htail

example (program : List YulEvmCompiler.Asm)
    (lookup : YulEvmCompiler.CertLookup)
    (entries : List Challenge.EvmProof.StackCertificate.FrozenStackEntry) :
    Challenge.EvmProof.StackCertificate.frozenEntryChecks
        program lookup entries =
      Challenge.EvmProof.StackCertificate.lengthEntryChecks
        program lookup
          (Challenge.EvmProof.StackCertificate.certificateData
            program entries).entries :=
  Challenge.EvmProof.StackCertificate.frozenEntryChecks_eq_lengthEntryChecks
    program lookup entries

/-- info: 'Challenge.EvmProof.StackCertificate.frozenEntryChecks_eq_lengthEntryChecks' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.StackCertificate.frozenEntryChecks_eq_lengthEntryChecks

/-- info: 'Challenge.EvmProof.StackCertificate.frozenEntryChecks_ten_parts' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Challenge.EvmProof.StackCertificate.frozenEntryChecks_ten_parts

/-- info: 'Challenge.EvmProof.StackCertificate.indexedEntryChecks_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.StackCertificate.indexedEntryChecks_eq

/-- info: 'Challenge.EvmProof.StackCertificate.checkedCert_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.StackCertificate.checkedCert_valid

/-- info: 'Challenge.EvmProof.StackCertificate.assembly_stack_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.StackCertificate.assembly_stack_bound
