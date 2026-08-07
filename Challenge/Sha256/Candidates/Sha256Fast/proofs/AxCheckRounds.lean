import Rounds8

/-! Axiom footprint of the checked tier: the 32-bit layer, the composition
lemma, every block lemma of the loop body, and loop control.  `verify.sh`
fails if any output here mentions anything beyond `propext`,
`Classical.choice` and `Quot.sound`. -/

#print axioms Challenge.Sha256.Fast.gadget_rot3
#print axioms Challenge.Sha256.Fast.gadget_rot2_shr
#print axioms Challenge.Sha256.Fast.rawRound_correct
#print axioms Challenge.Sha256.Fast.rawSchedule_correct
#print axioms Challenge.Sha256.Fast.runLocatedBlock_append

#print axioms Loop.round0
#print axioms Loop.round1
#print axioms Loop.round2
#print axioms Loop.round3
#print axioms Loop.round4
#print axioms Loop.round5
#print axioms Loop.round6
#print axioms Loop.round7
#print axioms Loop.ctrl_continue
