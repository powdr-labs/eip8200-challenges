import Challenge.EvmProof.Stepper
import Challenge.Sha256.Reference.Proofs.Bytecode.Functions
set_option warningAsError true
set_option maxRecDepth 10000
/-!
# The two big-sigma blocks

`Sigma1` is inlined into the round body; `Sigma0` is still a called function, with
a one-slot frame (`[x, returnAddress]`) rather than the old two-slot
`[x, output, returnAddress]`.  The backend made that choice per site, so the two
are not symmetric and cannot share a summary.

Each is three inlined rotations XOR-ed together — the sites `Functions` certifies
individually — so the old four-path decomposition
(`Setup`/`Middle1`/`Middle2`/`Finish`), which existed to bracket four `rotr`
*calls*, is replaced by one straight run each.
-/

namespace Challenge.Sha256.Reference.Proofs.Bytecode.BigSigma

open EvmSemantics
open EvmSemantics.EVM

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

open Functions (maskedRotr)

/-- `Sigma1 x = rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25`, in the association and
with the literal complements the bytecode uses. -/
def sigma1Word (x : UInt256) : UInt256 :=
  UInt256.xor
    (UInt256.xor (maskedRotr x (UInt256.ofNat 6) 0x1a)
      (maskedRotr x (UInt256.ofNat 11) 0x15))
    (maskedRotr x (UInt256.ofNat 25) 7)

/-- `Sigma0 x = rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22`. -/
def sigma0Word (x : UInt256) : UInt256 :=
  UInt256.xor
    (UInt256.xor (maskedRotr x (UInt256.ofNat 2) 0x1e)
      (maskedRotr x (UInt256.ofNat 13) 0x13))
    (maskedRotr x (UInt256.ofNat 22) 0xa)

@[simp] private theorem pc236 :
    Artifact.referenceArtifact.instructionPC 236 = 639 := by decide

@[simp] private theorem pc237 :
    Artifact.referenceArtifact.instructionPC 237 = 641 := by decide

@[simp] private theorem pc238 :
    Artifact.referenceArtifact.instructionPC 238 = 646 := by decide

@[simp] private theorem pc239 :
    Artifact.referenceArtifact.instructionPC 239 = 647 := by decide

@[simp] private theorem pc240 :
    Artifact.referenceArtifact.instructionPC 240 = 649 := by decide

@[simp] private theorem pc241 :
    Artifact.referenceArtifact.instructionPC 241 = 650 := by decide

@[simp] private theorem pc242 :
    Artifact.referenceArtifact.instructionPC 242 = 651 := by decide

@[simp] private theorem pc243 :
    Artifact.referenceArtifact.instructionPC 243 = 652 := by decide

@[simp] private theorem pc244 :
    Artifact.referenceArtifact.instructionPC 244 = 653 := by decide

@[simp] private theorem pc245 :
    Artifact.referenceArtifact.instructionPC 245 = 654 := by decide

@[simp] private theorem pc246 :
    Artifact.referenceArtifact.instructionPC 246 = 655 := by decide

@[simp] private theorem pc247 :
    Artifact.referenceArtifact.instructionPC 247 = 656 := by decide

@[simp] private theorem pc248 :
    Artifact.referenceArtifact.instructionPC 248 = 657 := by decide

@[simp] private theorem pc249 :
    Artifact.referenceArtifact.instructionPC 249 = 659 := by decide

@[simp] private theorem pc250 :
    Artifact.referenceArtifact.instructionPC 250 = 664 := by decide

@[simp] private theorem pc251 :
    Artifact.referenceArtifact.instructionPC 251 = 665 := by decide

@[simp] private theorem pc252 :
    Artifact.referenceArtifact.instructionPC 252 = 667 := by decide

@[simp] private theorem pc253 :
    Artifact.referenceArtifact.instructionPC 253 = 668 := by decide

@[simp] private theorem pc254 :
    Artifact.referenceArtifact.instructionPC 254 = 669 := by decide

@[simp] private theorem pc255 :
    Artifact.referenceArtifact.instructionPC 255 = 670 := by decide

@[simp] private theorem pc256 :
    Artifact.referenceArtifact.instructionPC 256 = 671 := by decide

@[simp] private theorem pc257 :
    Artifact.referenceArtifact.instructionPC 257 = 672 := by decide

@[simp] private theorem pc258 :
    Artifact.referenceArtifact.instructionPC 258 = 673 := by decide

@[simp] private theorem pc259 :
    Artifact.referenceArtifact.instructionPC 259 = 674 := by decide

@[simp] private theorem pc260 :
    Artifact.referenceArtifact.instructionPC 260 = 675 := by decide

@[simp] private theorem pc261 :
    Artifact.referenceArtifact.instructionPC 261 = 677 := by decide

@[simp] private theorem pc262 :
    Artifact.referenceArtifact.instructionPC 262 = 682 := by decide

@[simp] private theorem pc263 :
    Artifact.referenceArtifact.instructionPC 263 = 683 := by decide

@[simp] private theorem pc264 :
    Artifact.referenceArtifact.instructionPC 264 = 685 := by decide

@[simp] private theorem pc265 :
    Artifact.referenceArtifact.instructionPC 265 = 686 := by decide

@[simp] private theorem pc266 :
    Artifact.referenceArtifact.instructionPC 266 = 687 := by decide

@[simp] private theorem pc267 :
    Artifact.referenceArtifact.instructionPC 267 = 688 := by decide

@[simp] private theorem pc268 :
    Artifact.referenceArtifact.instructionPC 268 = 689 := by decide

@[simp] private theorem pc269 :
    Artifact.referenceArtifact.instructionPC 269 = 690 := by decide

@[simp] private theorem pc270 :
    Artifact.referenceArtifact.instructionPC 270 = 691 := by decide

@[simp] private theorem pc271 :
    Artifact.referenceArtifact.instructionPC 271 = 692 := by decide

@[simp] private theorem pc272 :
    Artifact.referenceArtifact.instructionPC 272 = 693 := by decide

@[simp] private theorem pc273 :
    Artifact.referenceArtifact.instructionPC 273 = 694 := by decide

@[simp] private theorem pc274 :
    Artifact.referenceArtifact.instructionPC 274 = 695 := by decide

@[simp] private theorem pc827 :
    Artifact.referenceArtifact.instructionPC 827 = 1564 := by decide

@[simp] private theorem pc828 :
    Artifact.referenceArtifact.instructionPC 828 = 1565 := by decide

@[simp] private theorem pc829 :
    Artifact.referenceArtifact.instructionPC 829 = 1567 := by decide

@[simp] private theorem pc830 :
    Artifact.referenceArtifact.instructionPC 830 = 1572 := by decide

@[simp] private theorem pc831 :
    Artifact.referenceArtifact.instructionPC 831 = 1573 := by decide

@[simp] private theorem pc832 :
    Artifact.referenceArtifact.instructionPC 832 = 1575 := by decide

@[simp] private theorem pc833 :
    Artifact.referenceArtifact.instructionPC 833 = 1576 := by decide

@[simp] private theorem pc834 :
    Artifact.referenceArtifact.instructionPC 834 = 1577 := by decide

@[simp] private theorem pc835 :
    Artifact.referenceArtifact.instructionPC 835 = 1578 := by decide

@[simp] private theorem pc836 :
    Artifact.referenceArtifact.instructionPC 836 = 1579 := by decide

@[simp] private theorem pc837 :
    Artifact.referenceArtifact.instructionPC 837 = 1580 := by decide

@[simp] private theorem pc838 :
    Artifact.referenceArtifact.instructionPC 838 = 1581 := by decide

@[simp] private theorem pc839 :
    Artifact.referenceArtifact.instructionPC 839 = 1582 := by decide

@[simp] private theorem pc840 :
    Artifact.referenceArtifact.instructionPC 840 = 1583 := by decide

@[simp] private theorem pc841 :
    Artifact.referenceArtifact.instructionPC 841 = 1585 := by decide

@[simp] private theorem pc842 :
    Artifact.referenceArtifact.instructionPC 842 = 1590 := by decide

@[simp] private theorem pc843 :
    Artifact.referenceArtifact.instructionPC 843 = 1591 := by decide

@[simp] private theorem pc844 :
    Artifact.referenceArtifact.instructionPC 844 = 1593 := by decide

@[simp] private theorem pc845 :
    Artifact.referenceArtifact.instructionPC 845 = 1594 := by decide

@[simp] private theorem pc846 :
    Artifact.referenceArtifact.instructionPC 846 = 1595 := by decide

@[simp] private theorem pc847 :
    Artifact.referenceArtifact.instructionPC 847 = 1596 := by decide

@[simp] private theorem pc848 :
    Artifact.referenceArtifact.instructionPC 848 = 1597 := by decide

@[simp] private theorem pc849 :
    Artifact.referenceArtifact.instructionPC 849 = 1598 := by decide

@[simp] private theorem pc850 :
    Artifact.referenceArtifact.instructionPC 850 = 1599 := by decide

@[simp] private theorem pc851 :
    Artifact.referenceArtifact.instructionPC 851 = 1600 := by decide

@[simp] private theorem pc852 :
    Artifact.referenceArtifact.instructionPC 852 = 1601 := by decide

@[simp] private theorem pc853 :
    Artifact.referenceArtifact.instructionPC 853 = 1603 := by decide

@[simp] private theorem pc854 :
    Artifact.referenceArtifact.instructionPC 854 = 1608 := by decide

@[simp] private theorem pc855 :
    Artifact.referenceArtifact.instructionPC 855 = 1609 := by decide

@[simp] private theorem pc856 :
    Artifact.referenceArtifact.instructionPC 856 = 1611 := by decide

@[simp] private theorem pc857 :
    Artifact.referenceArtifact.instructionPC 857 = 1612 := by decide

@[simp] private theorem pc858 :
    Artifact.referenceArtifact.instructionPC 858 = 1613 := by decide

@[simp] private theorem pc859 :
    Artifact.referenceArtifact.instructionPC 859 = 1614 := by decide

@[simp] private theorem pc860 :
    Artifact.referenceArtifact.instructionPC 860 = 1615 := by decide

@[simp] private theorem pc861 :
    Artifact.referenceArtifact.instructionPC 861 = 1616 := by decide

@[simp] private theorem pc862 :
    Artifact.referenceArtifact.instructionPC 862 = 1617 := by decide

@[simp] private theorem pc863 :
    Artifact.referenceArtifact.instructionPC 863 = 1618 := by decide

@[simp] private theorem pc864 :
    Artifact.referenceArtifact.instructionPC 864 = 1619 := by decide

@[simp] private theorem pc865 :
    Artifact.referenceArtifact.instructionPC 865 = 1620 := by decide

@[simp] private theorem pc866 :
    Artifact.referenceArtifact.instructionPC 866 = 1621 := by decide

@[simp] private theorem pc867 :
    Artifact.referenceArtifact.instructionPC 867 = 1622 := by decide

@[simp] private theorem pc868 :
    Artifact.referenceArtifact.instructionPC 868 = 1623 := by decide

@[simp] private theorem pc869 :
    Artifact.referenceArtifact.instructionPC 869 = 1624 := by decide

@[simp] private theorem pc870 :
    Artifact.referenceArtifact.instructionPC 870 = 1625 := by decide

@[simp] private theorem toNat639 : (UInt256.ofNat 639).toNat = 639 := by decide
@[simp] private theorem toNat641 : (UInt256.ofNat 641).toNat = 641 := by decide
@[simp] private theorem toNat646 : (UInt256.ofNat 646).toNat = 646 := by decide
@[simp] private theorem toNat647 : (UInt256.ofNat 647).toNat = 647 := by decide
@[simp] private theorem toNat649 : (UInt256.ofNat 649).toNat = 649 := by decide
@[simp] private theorem toNat650 : (UInt256.ofNat 650).toNat = 650 := by decide
@[simp] private theorem toNat651 : (UInt256.ofNat 651).toNat = 651 := by decide
@[simp] private theorem toNat652 : (UInt256.ofNat 652).toNat = 652 := by decide
@[simp] private theorem toNat653 : (UInt256.ofNat 653).toNat = 653 := by decide
@[simp] private theorem toNat654 : (UInt256.ofNat 654).toNat = 654 := by decide
@[simp] private theorem toNat655 : (UInt256.ofNat 655).toNat = 655 := by decide
@[simp] private theorem toNat656 : (UInt256.ofNat 656).toNat = 656 := by decide
@[simp] private theorem toNat657 : (UInt256.ofNat 657).toNat = 657 := by decide
@[simp] private theorem toNat659 : (UInt256.ofNat 659).toNat = 659 := by decide
@[simp] private theorem toNat664 : (UInt256.ofNat 664).toNat = 664 := by decide
@[simp] private theorem toNat665 : (UInt256.ofNat 665).toNat = 665 := by decide
@[simp] private theorem toNat667 : (UInt256.ofNat 667).toNat = 667 := by decide
@[simp] private theorem toNat668 : (UInt256.ofNat 668).toNat = 668 := by decide
@[simp] private theorem toNat669 : (UInt256.ofNat 669).toNat = 669 := by decide
@[simp] private theorem toNat670 : (UInt256.ofNat 670).toNat = 670 := by decide
@[simp] private theorem toNat671 : (UInt256.ofNat 671).toNat = 671 := by decide
@[simp] private theorem toNat672 : (UInt256.ofNat 672).toNat = 672 := by decide
@[simp] private theorem toNat673 : (UInt256.ofNat 673).toNat = 673 := by decide
@[simp] private theorem toNat674 : (UInt256.ofNat 674).toNat = 674 := by decide
@[simp] private theorem toNat675 : (UInt256.ofNat 675).toNat = 675 := by decide
@[simp] private theorem toNat677 : (UInt256.ofNat 677).toNat = 677 := by decide
@[simp] private theorem toNat682 : (UInt256.ofNat 682).toNat = 682 := by decide
@[simp] private theorem toNat683 : (UInt256.ofNat 683).toNat = 683 := by decide
@[simp] private theorem toNat685 : (UInt256.ofNat 685).toNat = 685 := by decide
@[simp] private theorem toNat686 : (UInt256.ofNat 686).toNat = 686 := by decide
@[simp] private theorem toNat687 : (UInt256.ofNat 687).toNat = 687 := by decide
@[simp] private theorem toNat688 : (UInt256.ofNat 688).toNat = 688 := by decide
@[simp] private theorem toNat689 : (UInt256.ofNat 689).toNat = 689 := by decide
@[simp] private theorem toNat690 : (UInt256.ofNat 690).toNat = 690 := by decide
@[simp] private theorem toNat691 : (UInt256.ofNat 691).toNat = 691 := by decide
@[simp] private theorem toNat692 : (UInt256.ofNat 692).toNat = 692 := by decide
@[simp] private theorem toNat693 : (UInt256.ofNat 693).toNat = 693 := by decide
@[simp] private theorem toNat694 : (UInt256.ofNat 694).toNat = 694 := by decide
@[simp] private theorem toNat695 : (UInt256.ofNat 695).toNat = 695 := by decide
@[simp] private theorem toNat1564 : (UInt256.ofNat 1564).toNat = 1564 := by decide
@[simp] private theorem toNat1565 : (UInt256.ofNat 1565).toNat = 1565 := by decide
@[simp] private theorem toNat1567 : (UInt256.ofNat 1567).toNat = 1567 := by decide
@[simp] private theorem toNat1572 : (UInt256.ofNat 1572).toNat = 1572 := by decide
@[simp] private theorem toNat1573 : (UInt256.ofNat 1573).toNat = 1573 := by decide
@[simp] private theorem toNat1575 : (UInt256.ofNat 1575).toNat = 1575 := by decide
@[simp] private theorem toNat1576 : (UInt256.ofNat 1576).toNat = 1576 := by decide
@[simp] private theorem toNat1577 : (UInt256.ofNat 1577).toNat = 1577 := by decide
@[simp] private theorem toNat1578 : (UInt256.ofNat 1578).toNat = 1578 := by decide
@[simp] private theorem toNat1579 : (UInt256.ofNat 1579).toNat = 1579 := by decide
@[simp] private theorem toNat1580 : (UInt256.ofNat 1580).toNat = 1580 := by decide
@[simp] private theorem toNat1581 : (UInt256.ofNat 1581).toNat = 1581 := by decide
@[simp] private theorem toNat1582 : (UInt256.ofNat 1582).toNat = 1582 := by decide
@[simp] private theorem toNat1583 : (UInt256.ofNat 1583).toNat = 1583 := by decide
@[simp] private theorem toNat1585 : (UInt256.ofNat 1585).toNat = 1585 := by decide
@[simp] private theorem toNat1590 : (UInt256.ofNat 1590).toNat = 1590 := by decide
@[simp] private theorem toNat1591 : (UInt256.ofNat 1591).toNat = 1591 := by decide
@[simp] private theorem toNat1593 : (UInt256.ofNat 1593).toNat = 1593 := by decide
@[simp] private theorem toNat1594 : (UInt256.ofNat 1594).toNat = 1594 := by decide
@[simp] private theorem toNat1595 : (UInt256.ofNat 1595).toNat = 1595 := by decide
@[simp] private theorem toNat1596 : (UInt256.ofNat 1596).toNat = 1596 := by decide
@[simp] private theorem toNat1597 : (UInt256.ofNat 1597).toNat = 1597 := by decide
@[simp] private theorem toNat1598 : (UInt256.ofNat 1598).toNat = 1598 := by decide
@[simp] private theorem toNat1599 : (UInt256.ofNat 1599).toNat = 1599 := by decide
@[simp] private theorem toNat1600 : (UInt256.ofNat 1600).toNat = 1600 := by decide
@[simp] private theorem toNat1601 : (UInt256.ofNat 1601).toNat = 1601 := by decide
@[simp] private theorem toNat1603 : (UInt256.ofNat 1603).toNat = 1603 := by decide
@[simp] private theorem toNat1608 : (UInt256.ofNat 1608).toNat = 1608 := by decide
@[simp] private theorem toNat1609 : (UInt256.ofNat 1609).toNat = 1609 := by decide
@[simp] private theorem toNat1611 : (UInt256.ofNat 1611).toNat = 1611 := by decide
@[simp] private theorem toNat1612 : (UInt256.ofNat 1612).toNat = 1612 := by decide
@[simp] private theorem toNat1613 : (UInt256.ofNat 1613).toNat = 1613 := by decide
@[simp] private theorem toNat1614 : (UInt256.ofNat 1614).toNat = 1614 := by decide
@[simp] private theorem toNat1615 : (UInt256.ofNat 1615).toNat = 1615 := by decide
@[simp] private theorem toNat1616 : (UInt256.ofNat 1616).toNat = 1616 := by decide
@[simp] private theorem toNat1617 : (UInt256.ofNat 1617).toNat = 1617 := by decide
@[simp] private theorem toNat1618 : (UInt256.ofNat 1618).toNat = 1618 := by decide
@[simp] private theorem toNat1619 : (UInt256.ofNat 1619).toNat = 1619 := by decide
@[simp] private theorem toNat1620 : (UInt256.ofNat 1620).toNat = 1620 := by decide
@[simp] private theorem toNat1621 : (UInt256.ofNat 1621).toNat = 1621 := by decide
@[simp] private theorem toNat1622 : (UInt256.ofNat 1622).toNat = 1622 := by decide
@[simp] private theorem toNat1623 : (UInt256.ofNat 1623).toNat = 1623 := by decide
@[simp] private theorem toNat1624 : (UInt256.ofNat 1624).toNat = 1624 := by decide
@[simp] private theorem toNat1625 : (UInt256.ofNat 1625).toNat = 1625 := by decide

@[simp] private theorem next236 : UInt256.ofNat 639 + UInt256.ofNat 2 = UInt256.ofNat 641 := by decide
@[simp] private theorem next237 : UInt256.ofNat 641 + UInt256.ofNat 5 = UInt256.ofNat 646 := by decide
@[simp] private theorem next238 : (UInt256.ofNat 646).succ = UInt256.ofNat 647 := by decide
@[simp] private theorem next239 : UInt256.ofNat 647 + UInt256.ofNat 2 = UInt256.ofNat 649 := by decide
@[simp] private theorem next240 : (UInt256.ofNat 649).succ = UInt256.ofNat 650 := by decide
@[simp] private theorem next241 : (UInt256.ofNat 650).succ = UInt256.ofNat 651 := by decide
@[simp] private theorem next242 : (UInt256.ofNat 651).succ = UInt256.ofNat 652 := by decide
@[simp] private theorem next243 : (UInt256.ofNat 652).succ = UInt256.ofNat 653 := by decide
@[simp] private theorem next244 : (UInt256.ofNat 653).succ = UInt256.ofNat 654 := by decide
@[simp] private theorem next245 : (UInt256.ofNat 654).succ = UInt256.ofNat 655 := by decide
@[simp] private theorem next246 : (UInt256.ofNat 655).succ = UInt256.ofNat 656 := by decide
@[simp] private theorem next247 : (UInt256.ofNat 656).succ = UInt256.ofNat 657 := by decide
@[simp] private theorem next248 : UInt256.ofNat 657 + UInt256.ofNat 2 = UInt256.ofNat 659 := by decide
@[simp] private theorem next249 : UInt256.ofNat 659 + UInt256.ofNat 5 = UInt256.ofNat 664 := by decide
@[simp] private theorem next250 : (UInt256.ofNat 664).succ = UInt256.ofNat 665 := by decide
@[simp] private theorem next251 : UInt256.ofNat 665 + UInt256.ofNat 2 = UInt256.ofNat 667 := by decide
@[simp] private theorem next252 : (UInt256.ofNat 667).succ = UInt256.ofNat 668 := by decide
@[simp] private theorem next253 : (UInt256.ofNat 668).succ = UInt256.ofNat 669 := by decide
@[simp] private theorem next254 : (UInt256.ofNat 669).succ = UInt256.ofNat 670 := by decide
@[simp] private theorem next255 : (UInt256.ofNat 670).succ = UInt256.ofNat 671 := by decide
@[simp] private theorem next256 : (UInt256.ofNat 671).succ = UInt256.ofNat 672 := by decide
@[simp] private theorem next257 : (UInt256.ofNat 672).succ = UInt256.ofNat 673 := by decide
@[simp] private theorem next258 : (UInt256.ofNat 673).succ = UInt256.ofNat 674 := by decide
@[simp] private theorem next259 : (UInt256.ofNat 674).succ = UInt256.ofNat 675 := by decide
@[simp] private theorem next260 : UInt256.ofNat 675 + UInt256.ofNat 2 = UInt256.ofNat 677 := by decide
@[simp] private theorem next261 : UInt256.ofNat 677 + UInt256.ofNat 5 = UInt256.ofNat 682 := by decide
@[simp] private theorem next262 : (UInt256.ofNat 682).succ = UInt256.ofNat 683 := by decide
@[simp] private theorem next263 : UInt256.ofNat 683 + UInt256.ofNat 2 = UInt256.ofNat 685 := by decide
@[simp] private theorem next264 : (UInt256.ofNat 685).succ = UInt256.ofNat 686 := by decide
@[simp] private theorem next265 : (UInt256.ofNat 686).succ = UInt256.ofNat 687 := by decide
@[simp] private theorem next266 : (UInt256.ofNat 687).succ = UInt256.ofNat 688 := by decide
@[simp] private theorem next267 : (UInt256.ofNat 688).succ = UInt256.ofNat 689 := by decide
@[simp] private theorem next268 : (UInt256.ofNat 689).succ = UInt256.ofNat 690 := by decide
@[simp] private theorem next269 : (UInt256.ofNat 690).succ = UInt256.ofNat 691 := by decide
@[simp] private theorem next270 : (UInt256.ofNat 691).succ = UInt256.ofNat 692 := by decide
@[simp] private theorem next271 : (UInt256.ofNat 692).succ = UInt256.ofNat 693 := by decide
@[simp] private theorem next272 : (UInt256.ofNat 693).succ = UInt256.ofNat 694 := by decide
@[simp] private theorem next273 : (UInt256.ofNat 694).succ = UInt256.ofNat 695 := by decide
@[simp] private theorem next827 : (UInt256.ofNat 1564).succ = UInt256.ofNat 1565 := by decide
@[simp] private theorem next828 : UInt256.ofNat 1565 + UInt256.ofNat 2 = UInt256.ofNat 1567 := by decide
@[simp] private theorem next829 : UInt256.ofNat 1567 + UInt256.ofNat 5 = UInt256.ofNat 1572 := by decide
@[simp] private theorem next830 : (UInt256.ofNat 1572).succ = UInt256.ofNat 1573 := by decide
@[simp] private theorem next831 : UInt256.ofNat 1573 + UInt256.ofNat 2 = UInt256.ofNat 1575 := by decide
@[simp] private theorem next832 : (UInt256.ofNat 1575).succ = UInt256.ofNat 1576 := by decide
@[simp] private theorem next833 : (UInt256.ofNat 1576).succ = UInt256.ofNat 1577 := by decide
@[simp] private theorem next834 : (UInt256.ofNat 1577).succ = UInt256.ofNat 1578 := by decide
@[simp] private theorem next835 : (UInt256.ofNat 1578).succ = UInt256.ofNat 1579 := by decide
@[simp] private theorem next836 : (UInt256.ofNat 1579).succ = UInt256.ofNat 1580 := by decide
@[simp] private theorem next837 : (UInt256.ofNat 1580).succ = UInt256.ofNat 1581 := by decide
@[simp] private theorem next838 : (UInt256.ofNat 1581).succ = UInt256.ofNat 1582 := by decide
@[simp] private theorem next839 : (UInt256.ofNat 1582).succ = UInt256.ofNat 1583 := by decide
@[simp] private theorem next840 : UInt256.ofNat 1583 + UInt256.ofNat 2 = UInt256.ofNat 1585 := by decide
@[simp] private theorem next841 : UInt256.ofNat 1585 + UInt256.ofNat 5 = UInt256.ofNat 1590 := by decide
@[simp] private theorem next842 : (UInt256.ofNat 1590).succ = UInt256.ofNat 1591 := by decide
@[simp] private theorem next843 : UInt256.ofNat 1591 + UInt256.ofNat 2 = UInt256.ofNat 1593 := by decide
@[simp] private theorem next844 : (UInt256.ofNat 1593).succ = UInt256.ofNat 1594 := by decide
@[simp] private theorem next845 : (UInt256.ofNat 1594).succ = UInt256.ofNat 1595 := by decide
@[simp] private theorem next846 : (UInt256.ofNat 1595).succ = UInt256.ofNat 1596 := by decide
@[simp] private theorem next847 : (UInt256.ofNat 1596).succ = UInt256.ofNat 1597 := by decide
@[simp] private theorem next848 : (UInt256.ofNat 1597).succ = UInt256.ofNat 1598 := by decide
@[simp] private theorem next849 : (UInt256.ofNat 1598).succ = UInt256.ofNat 1599 := by decide
@[simp] private theorem next850 : (UInt256.ofNat 1599).succ = UInt256.ofNat 1600 := by decide
@[simp] private theorem next851 : (UInt256.ofNat 1600).succ = UInt256.ofNat 1601 := by decide
@[simp] private theorem next852 : UInt256.ofNat 1601 + UInt256.ofNat 2 = UInt256.ofNat 1603 := by decide
@[simp] private theorem next853 : UInt256.ofNat 1603 + UInt256.ofNat 5 = UInt256.ofNat 1608 := by decide
@[simp] private theorem next854 : (UInt256.ofNat 1608).succ = UInt256.ofNat 1609 := by decide
@[simp] private theorem next855 : UInt256.ofNat 1609 + UInt256.ofNat 2 = UInt256.ofNat 1611 := by decide
@[simp] private theorem next856 : (UInt256.ofNat 1611).succ = UInt256.ofNat 1612 := by decide
@[simp] private theorem next857 : (UInt256.ofNat 1612).succ = UInt256.ofNat 1613 := by decide
@[simp] private theorem next858 : (UInt256.ofNat 1613).succ = UInt256.ofNat 1614 := by decide
@[simp] private theorem next859 : (UInt256.ofNat 1614).succ = UInt256.ofNat 1615 := by decide
@[simp] private theorem next860 : (UInt256.ofNat 1615).succ = UInt256.ofNat 1616 := by decide
@[simp] private theorem next861 : (UInt256.ofNat 1616).succ = UInt256.ofNat 1617 := by decide
@[simp] private theorem next862 : (UInt256.ofNat 1617).succ = UInt256.ofNat 1618 := by decide
@[simp] private theorem next863 : (UInt256.ofNat 1618).succ = UInt256.ofNat 1619 := by decide
@[simp] private theorem next864 : (UInt256.ofNat 1619).succ = UInt256.ofNat 1620 := by decide
@[simp] private theorem next865 : (UInt256.ofNat 1620).succ = UInt256.ofNat 1621 := by decide
@[simp] private theorem next866 : (UInt256.ofNat 1621).succ = UInt256.ofNat 1622 := by decide
@[simp] private theorem next867 : (UInt256.ofNat 1622).succ = UInt256.ofNat 1623 := by decide
@[simp] private theorem next868 : (UInt256.ofNat 1623).succ = UInt256.ofNat 1624 := by decide
@[simp] private theorem next869 : (UInt256.ofNat 1624).succ = UInt256.ofNat 1625 := by decide

/-- The inlined `Sigma1`: instructions 236..273, pushing `sigma1Word` of the
word two slots down. -/
def sigma1Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨236, .push ⟨1, by decide⟩ (UInt256.ofNat 25), by rfl, by decide⟩,
   ⟨237, .push ⟨4, by decide⟩ (UInt256.ofNat 4294967295), by rfl, by decide⟩,
   ⟨238, .op (.Dup ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨239, .push ⟨1, by decide⟩ (UInt256.ofNat 7), by rfl, by decide⟩,
   ⟨240, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨241, .op (.Dup ⟨5, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨242, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨243, .op (.Swap ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨244, .op (.Swap ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨245, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨246, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨247, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨248, .push ⟨1, by decide⟩ (UInt256.ofNat 11), by rfl, by decide⟩,
   ⟨249, .push ⟨4, by decide⟩ (UInt256.ofNat 4294967295), by rfl, by decide⟩,
   ⟨250, .op (.Dup ⟨5, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨251, .push ⟨1, by decide⟩ (UInt256.ofNat 21), by rfl, by decide⟩,
   ⟨252, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨253, .op (.Dup ⟨6, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨254, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨255, .op (.Swap ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨256, .op (.Swap ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨257, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨258, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨259, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨260, .push ⟨1, by decide⟩ (UInt256.ofNat 6), by rfl, by decide⟩,
   ⟨261, .push ⟨4, by decide⟩ (UInt256.ofNat 4294967295), by rfl, by decide⟩,
   ⟨262, .op (.Dup ⟨6, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨263, .push ⟨1, by decide⟩ (UInt256.ofNat 26), by rfl, by decide⟩,
   ⟨264, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨265, .op (.Dup ⟨7, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨266, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨267, .op (.Swap ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨268, .op (.Swap ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨269, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨270, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨271, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨272, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨273, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩]

def sigma1Entry (s : State) (v0 v1 x : UInt256) (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat (Artifact.referenceArtifact.instructionPC 236)
    stack := v0 :: v1 :: x :: rest }

def sigma1Result (s : State) (v0 v1 x : UInt256) (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat (Artifact.referenceArtifact.instructionPC 274)
    stack := sigma1Word x :: v0 :: v1 :: x :: rest }

set_option maxHeartbeats 4000000 in
theorem run_sigma1 (s : State) (v0 v1 x : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock sigma1Path
      (sigma1Entry s v0 v1 x rest) = some (sigma1Result s v0 v1 x rest) := by
  have g3 : rest.length + 1 + 1 + 1 < 1024 := by omega
  have g4 : rest.length + 1 + 1 + 1 + 1 < 1024 := by omega
  have g5 : rest.length + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have g6 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have g7 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have g8 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have g9 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  simp [sigma1Path, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    sigma1Entry, sigma1Result, sigma1Word, maskedRotr, List.exchange,
    g3, g4, g5, g6, g7, g8, g9, hrun]

/-- The called `Sigma0`: entry `JUMPDEST` at 827 through the returning `JUMP` at
869, on the frame `[x, returnAddress]`. -/
def sigma0Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨827, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨828, .push ⟨1, by decide⟩ (UInt256.ofNat 22), by rfl, by decide⟩,
   ⟨829, .push ⟨4, by decide⟩ (UInt256.ofNat 4294967295), by rfl, by decide⟩,
   ⟨830, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨831, .push ⟨1, by decide⟩ (UInt256.ofNat 10), by rfl, by decide⟩,
   ⟨832, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨833, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨834, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨835, .op (.Swap ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨836, .op (.Swap ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨837, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨838, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨839, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨840, .push ⟨1, by decide⟩ (UInt256.ofNat 13), by rfl, by decide⟩,
   ⟨841, .push ⟨4, by decide⟩ (UInt256.ofNat 4294967295), by rfl, by decide⟩,
   ⟨842, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨843, .push ⟨1, by decide⟩ (UInt256.ofNat 19), by rfl, by decide⟩,
   ⟨844, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨845, .op (.Dup ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨846, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨847, .op (.Swap ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨848, .op (.Swap ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨849, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨850, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨851, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨852, .push ⟨1, by decide⟩ (UInt256.ofNat 2), by rfl, by decide⟩,
   ⟨853, .push ⟨4, by decide⟩ (UInt256.ofNat 4294967295), by rfl, by decide⟩,
   ⟨854, .op (.Dup ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨855, .push ⟨1, by decide⟩ (UInt256.ofNat 30), by rfl, by decide⟩,
   ⟨856, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨857, .op (.Swap ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨858, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨859, .op (.Swap ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨860, .op (.Swap ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨861, .op (.Swap ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨862, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨863, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨864, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨865, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨866, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨867, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨868, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨869, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def sigma0Entry (s : State) (x returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat (Artifact.referenceArtifact.instructionPC 827)
    stack := x :: returnDest :: rest }

def sigma0Returned (s : State) (x returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := returnDest
    stack := sigma0Word x :: rest }

set_option maxHeartbeats 4000000 in
theorem run_sigma0 (s : State) (x returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true)
    (hcode : s.executionEnv.code = referenceBytecode) :
    Challenge.EvmProof.Stepper.runLocatedBlock sigma0Path
      (sigma0Entry s x returnDest rest) =
        some (sigma0Returned s x returnDest rest) := by
  have g2 : rest.length + 1 + 1 < 1024 := by omega
  have g3 : rest.length + 1 + 1 + 1 < 1024 := by omega
  have g4 : rest.length + 1 + 1 + 1 + 1 < 1024 := by omega
  have g5 : rest.length + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have g6 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have g7 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have g8 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  simp [sigma0Path, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    sigma0Entry, sigma0Returned, sigma0Word, maskedRotr, List.exchange,
    g2, g3, g4, g5, g6, g7, g8, hrun, hvalid, hcode]

/-! ### `GasSteps` wrappers -/

def gasSteps_sigma1 (s : State) (v0 v1 x : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000)
    (hcode : (sigma1Entry s v0 v1 x rest).executionEnv.code = referenceBytecode)
    (hfork : (sigma1Entry s v0 v1 x rest).fork = .Osaka)
    (hrun : s.halt = .Running)
    (hhalt : (sigma1Entry s v0 v1 x rest).halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig
      (sigma1Entry s v0 v1 x rest).executionEnv.precompileConfig
      (sigma1Entry s v0 v1 x rest).executionEnv.fork
      (sigma1Entry s v0 v1 x rest).executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (sigma1Entry s v0 v1 x rest)
      (sigma1Result s v0 v1 x rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka sigma1Path
  · exact hcode
  · exact hfork
  · exact run_sigma1 s v0 v1 x rest hcap hrun
  · exact hhalt
  · exact hnp

def gasSteps_sigma0 (s : State) (x returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : (sigma0Entry s x returnDest rest).fork = .Osaka)
    (hrun : s.halt = .Running)
    (hhalt : (sigma0Entry s x returnDest rest).halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig
      (sigma0Entry s x returnDest rest).executionEnv.precompileConfig
      (sigma0Entry s x returnDest rest).executionEnv.fork
      (sigma0Entry s x returnDest rest).executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps (sigma0Entry s x returnDest rest)
      (sigma0Returned s x returnDest rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka sigma0Path
  · exact hcode
  · exact hfork
  · exact run_sigma0 s x returnDest rest hcap hrun hvalid hcode
  · exact hhalt
  · exact hnp

end Challenge.Sha256.Reference.Proofs.Bytecode.BigSigma
