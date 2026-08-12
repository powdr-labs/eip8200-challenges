import Challenge.EvmProof.ProfiledSteps

set_option warningAsError true

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

example {config : PrecompileConfig} {code : ByteArray} {s s' : State}
    (hstep : Step s s') (hf : FrameOK code s) (hf' : FrameOK code s')
    (hprofile : Challenge.EvmProof.CallerProfile config s) :
    Challenge.EvmProof.CallerProfile config s' :=
  Challenge.EvmProof.CallerProfile.step_between_frames hstep hf hf' hprofile

example {config : PrecompileConfig} {code : ByteArray} {s s' : State}
    (hsteps : Steps s s') (hf : FrameOK code s) (hf' : FrameOK code s')
    (hprofile : Challenge.EvmProof.CallerProfile config s) :
    Challenge.EvmProof.CallerProfile config s' :=
  Challenge.EvmProof.CallerProfile.steps_between_frames hsteps hf hf' hprofile

/-- info: 'Challenge.EvmProof.CallerProfile.step_between_frames' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.CallerProfile.step_between_frames

/-- info: 'Challenge.EvmProof.CallerProfile.steps_between_frames' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.CallerProfile.steps_between_frames
