import Challenge.EvmProof.Stepper
import Challenge.Sha256.Reference.Proofs.Bytecode.Trace
import Challenge.Sha256.Reference.Proofs.Bytecode.Word
set_option warningAsError true
set_option maxRecDepth 10000
/-!
# Certified summaries for the reference helper functions

The backend inlines the Yul helpers instead of compiling them to internal jumps,
so `rotr` has no function body to summarize once and no call frame: there is no
`output` slot and no return address anywhere here.  `unaryEntry`, `unaryReturned`
and `ternaryEntry`, which described that frame, are gone with it, as are the
`ch`/`maj`/`ssig0`/`ssig1` call paths.

`rotr` is spliced at ten sites in two shapes.  Both compute the same thing —
right-shift the word by the count on top of the stack, OR a left shift by the
literal complement, truncate to 32 bits — but they differ in stack discipline,
and the rotated word sits at a *different depth* at each site, so unlike the
memory accessors these cannot share one conclusion.  Each site therefore gets its
own summary; the proofs are the same script.

  shape A (11 instructions, rotated word retained):
    237 depth 3 shift 0x07     249 depth 4 shift 0x15
    261 depth 5 shift 0x1a     564 depth 2 shift 0x0e
    782 depth 2 shift 0x0d     829 depth 1 shift 0x0a
    841 depth 2 shift 0x13
  shape B (13 instructions, rotated word consumed):
    576 depth 3 shift 0x19     794 depth 3 shift 0x0f
    853 depth 3 shift 0x1e

The literal complement is only the right rotation when the count matches it; the
surrounding code is what guarantees that, so these summaries state the expression
the bytecode computes and leave the relation to `Word.rotr` to the callers.
-/

namespace Challenge.Sha256.Reference.Proofs.Bytecode.Functions

open EvmSemantics
open EvmSemantics.EVM

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

/-- The expression an inlined rotate site computes. -/
def maskedRotr (v count : UInt256) (shift : Nat) : UInt256 :=
  UInt256.land
    (UInt256.lor (UInt256.shiftRight v count)
      (UInt256.shiftLeft v (UInt256.ofNat shift)))
    (UInt256.ofNat 4294967295)

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

@[simp] private theorem pc564 :
    Artifact.referenceArtifact.instructionPC 564 = 1156 := by decide

@[simp] private theorem pc565 :
    Artifact.referenceArtifact.instructionPC 565 = 1161 := by decide

@[simp] private theorem pc566 :
    Artifact.referenceArtifact.instructionPC 566 = 1162 := by decide

@[simp] private theorem pc567 :
    Artifact.referenceArtifact.instructionPC 567 = 1164 := by decide

@[simp] private theorem pc568 :
    Artifact.referenceArtifact.instructionPC 568 = 1165 := by decide

@[simp] private theorem pc569 :
    Artifact.referenceArtifact.instructionPC 569 = 1166 := by decide

@[simp] private theorem pc570 :
    Artifact.referenceArtifact.instructionPC 570 = 1167 := by decide

@[simp] private theorem pc571 :
    Artifact.referenceArtifact.instructionPC 571 = 1168 := by decide

@[simp] private theorem pc572 :
    Artifact.referenceArtifact.instructionPC 572 = 1169 := by decide

@[simp] private theorem pc573 :
    Artifact.referenceArtifact.instructionPC 573 = 1170 := by decide

@[simp] private theorem pc574 :
    Artifact.referenceArtifact.instructionPC 574 = 1171 := by decide

@[simp] private theorem pc575 :
    Artifact.referenceArtifact.instructionPC 575 = 1172 := by decide

@[simp] private theorem pc576 :
    Artifact.referenceArtifact.instructionPC 576 = 1174 := by decide

@[simp] private theorem pc577 :
    Artifact.referenceArtifact.instructionPC 577 = 1179 := by decide

@[simp] private theorem pc578 :
    Artifact.referenceArtifact.instructionPC 578 = 1180 := by decide

@[simp] private theorem pc579 :
    Artifact.referenceArtifact.instructionPC 579 = 1182 := by decide

@[simp] private theorem pc580 :
    Artifact.referenceArtifact.instructionPC 580 = 1183 := by decide

@[simp] private theorem pc581 :
    Artifact.referenceArtifact.instructionPC 581 = 1184 := by decide

@[simp] private theorem pc582 :
    Artifact.referenceArtifact.instructionPC 582 = 1185 := by decide

@[simp] private theorem pc583 :
    Artifact.referenceArtifact.instructionPC 583 = 1186 := by decide

@[simp] private theorem pc584 :
    Artifact.referenceArtifact.instructionPC 584 = 1187 := by decide

@[simp] private theorem pc585 :
    Artifact.referenceArtifact.instructionPC 585 = 1188 := by decide

@[simp] private theorem pc586 :
    Artifact.referenceArtifact.instructionPC 586 = 1189 := by decide

@[simp] private theorem pc587 :
    Artifact.referenceArtifact.instructionPC 587 = 1190 := by decide

@[simp] private theorem pc588 :
    Artifact.referenceArtifact.instructionPC 588 = 1191 := by decide

@[simp] private theorem pc589 :
    Artifact.referenceArtifact.instructionPC 589 = 1192 := by decide

@[simp] private theorem pc782 :
    Artifact.referenceArtifact.instructionPC 782 = 1508 := by decide

@[simp] private theorem pc783 :
    Artifact.referenceArtifact.instructionPC 783 = 1513 := by decide

@[simp] private theorem pc784 :
    Artifact.referenceArtifact.instructionPC 784 = 1514 := by decide

@[simp] private theorem pc785 :
    Artifact.referenceArtifact.instructionPC 785 = 1516 := by decide

@[simp] private theorem pc786 :
    Artifact.referenceArtifact.instructionPC 786 = 1517 := by decide

@[simp] private theorem pc787 :
    Artifact.referenceArtifact.instructionPC 787 = 1518 := by decide

@[simp] private theorem pc788 :
    Artifact.referenceArtifact.instructionPC 788 = 1519 := by decide

@[simp] private theorem pc789 :
    Artifact.referenceArtifact.instructionPC 789 = 1520 := by decide

@[simp] private theorem pc790 :
    Artifact.referenceArtifact.instructionPC 790 = 1521 := by decide

@[simp] private theorem pc791 :
    Artifact.referenceArtifact.instructionPC 791 = 1522 := by decide

@[simp] private theorem pc792 :
    Artifact.referenceArtifact.instructionPC 792 = 1523 := by decide

@[simp] private theorem pc793 :
    Artifact.referenceArtifact.instructionPC 793 = 1524 := by decide

@[simp] private theorem pc794 :
    Artifact.referenceArtifact.instructionPC 794 = 1526 := by decide

@[simp] private theorem pc795 :
    Artifact.referenceArtifact.instructionPC 795 = 1531 := by decide

@[simp] private theorem pc796 :
    Artifact.referenceArtifact.instructionPC 796 = 1532 := by decide

@[simp] private theorem pc797 :
    Artifact.referenceArtifact.instructionPC 797 = 1534 := by decide

@[simp] private theorem pc798 :
    Artifact.referenceArtifact.instructionPC 798 = 1535 := by decide

@[simp] private theorem pc799 :
    Artifact.referenceArtifact.instructionPC 799 = 1536 := by decide

@[simp] private theorem pc800 :
    Artifact.referenceArtifact.instructionPC 800 = 1537 := by decide

@[simp] private theorem pc801 :
    Artifact.referenceArtifact.instructionPC 801 = 1538 := by decide

@[simp] private theorem pc802 :
    Artifact.referenceArtifact.instructionPC 802 = 1539 := by decide

@[simp] private theorem pc803 :
    Artifact.referenceArtifact.instructionPC 803 = 1540 := by decide

@[simp] private theorem pc804 :
    Artifact.referenceArtifact.instructionPC 804 = 1541 := by decide

@[simp] private theorem pc805 :
    Artifact.referenceArtifact.instructionPC 805 = 1542 := by decide

@[simp] private theorem pc806 :
    Artifact.referenceArtifact.instructionPC 806 = 1543 := by decide

@[simp] private theorem pc807 :
    Artifact.referenceArtifact.instructionPC 807 = 1544 := by decide

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
@[simp] private theorem toNat1156 : (UInt256.ofNat 1156).toNat = 1156 := by decide
@[simp] private theorem toNat1161 : (UInt256.ofNat 1161).toNat = 1161 := by decide
@[simp] private theorem toNat1162 : (UInt256.ofNat 1162).toNat = 1162 := by decide
@[simp] private theorem toNat1164 : (UInt256.ofNat 1164).toNat = 1164 := by decide
@[simp] private theorem toNat1165 : (UInt256.ofNat 1165).toNat = 1165 := by decide
@[simp] private theorem toNat1166 : (UInt256.ofNat 1166).toNat = 1166 := by decide
@[simp] private theorem toNat1167 : (UInt256.ofNat 1167).toNat = 1167 := by decide
@[simp] private theorem toNat1168 : (UInt256.ofNat 1168).toNat = 1168 := by decide
@[simp] private theorem toNat1169 : (UInt256.ofNat 1169).toNat = 1169 := by decide
@[simp] private theorem toNat1170 : (UInt256.ofNat 1170).toNat = 1170 := by decide
@[simp] private theorem toNat1171 : (UInt256.ofNat 1171).toNat = 1171 := by decide
@[simp] private theorem toNat1172 : (UInt256.ofNat 1172).toNat = 1172 := by decide
@[simp] private theorem toNat1174 : (UInt256.ofNat 1174).toNat = 1174 := by decide
@[simp] private theorem toNat1179 : (UInt256.ofNat 1179).toNat = 1179 := by decide
@[simp] private theorem toNat1180 : (UInt256.ofNat 1180).toNat = 1180 := by decide
@[simp] private theorem toNat1182 : (UInt256.ofNat 1182).toNat = 1182 := by decide
@[simp] private theorem toNat1183 : (UInt256.ofNat 1183).toNat = 1183 := by decide
@[simp] private theorem toNat1184 : (UInt256.ofNat 1184).toNat = 1184 := by decide
@[simp] private theorem toNat1185 : (UInt256.ofNat 1185).toNat = 1185 := by decide
@[simp] private theorem toNat1186 : (UInt256.ofNat 1186).toNat = 1186 := by decide
@[simp] private theorem toNat1187 : (UInt256.ofNat 1187).toNat = 1187 := by decide
@[simp] private theorem toNat1188 : (UInt256.ofNat 1188).toNat = 1188 := by decide
@[simp] private theorem toNat1189 : (UInt256.ofNat 1189).toNat = 1189 := by decide
@[simp] private theorem toNat1190 : (UInt256.ofNat 1190).toNat = 1190 := by decide
@[simp] private theorem toNat1191 : (UInt256.ofNat 1191).toNat = 1191 := by decide
@[simp] private theorem toNat1192 : (UInt256.ofNat 1192).toNat = 1192 := by decide
@[simp] private theorem toNat1508 : (UInt256.ofNat 1508).toNat = 1508 := by decide
@[simp] private theorem toNat1513 : (UInt256.ofNat 1513).toNat = 1513 := by decide
@[simp] private theorem toNat1514 : (UInt256.ofNat 1514).toNat = 1514 := by decide
@[simp] private theorem toNat1516 : (UInt256.ofNat 1516).toNat = 1516 := by decide
@[simp] private theorem toNat1517 : (UInt256.ofNat 1517).toNat = 1517 := by decide
@[simp] private theorem toNat1518 : (UInt256.ofNat 1518).toNat = 1518 := by decide
@[simp] private theorem toNat1519 : (UInt256.ofNat 1519).toNat = 1519 := by decide
@[simp] private theorem toNat1520 : (UInt256.ofNat 1520).toNat = 1520 := by decide
@[simp] private theorem toNat1521 : (UInt256.ofNat 1521).toNat = 1521 := by decide
@[simp] private theorem toNat1522 : (UInt256.ofNat 1522).toNat = 1522 := by decide
@[simp] private theorem toNat1523 : (UInt256.ofNat 1523).toNat = 1523 := by decide
@[simp] private theorem toNat1524 : (UInt256.ofNat 1524).toNat = 1524 := by decide
@[simp] private theorem toNat1526 : (UInt256.ofNat 1526).toNat = 1526 := by decide
@[simp] private theorem toNat1531 : (UInt256.ofNat 1531).toNat = 1531 := by decide
@[simp] private theorem toNat1532 : (UInt256.ofNat 1532).toNat = 1532 := by decide
@[simp] private theorem toNat1534 : (UInt256.ofNat 1534).toNat = 1534 := by decide
@[simp] private theorem toNat1535 : (UInt256.ofNat 1535).toNat = 1535 := by decide
@[simp] private theorem toNat1536 : (UInt256.ofNat 1536).toNat = 1536 := by decide
@[simp] private theorem toNat1537 : (UInt256.ofNat 1537).toNat = 1537 := by decide
@[simp] private theorem toNat1538 : (UInt256.ofNat 1538).toNat = 1538 := by decide
@[simp] private theorem toNat1539 : (UInt256.ofNat 1539).toNat = 1539 := by decide
@[simp] private theorem toNat1540 : (UInt256.ofNat 1540).toNat = 1540 := by decide
@[simp] private theorem toNat1541 : (UInt256.ofNat 1541).toNat = 1541 := by decide
@[simp] private theorem toNat1542 : (UInt256.ofNat 1542).toNat = 1542 := by decide
@[simp] private theorem toNat1543 : (UInt256.ofNat 1543).toNat = 1543 := by decide
@[simp] private theorem toNat1544 : (UInt256.ofNat 1544).toNat = 1544 := by decide
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
@[simp] private theorem next564 : UInt256.ofNat 1156 + UInt256.ofNat 5 = UInt256.ofNat 1161 := by decide
@[simp] private theorem next565 : (UInt256.ofNat 1161).succ = UInt256.ofNat 1162 := by decide
@[simp] private theorem next566 : UInt256.ofNat 1162 + UInt256.ofNat 2 = UInt256.ofNat 1164 := by decide
@[simp] private theorem next567 : (UInt256.ofNat 1164).succ = UInt256.ofNat 1165 := by decide
@[simp] private theorem next568 : (UInt256.ofNat 1165).succ = UInt256.ofNat 1166 := by decide
@[simp] private theorem next569 : (UInt256.ofNat 1166).succ = UInt256.ofNat 1167 := by decide
@[simp] private theorem next570 : (UInt256.ofNat 1167).succ = UInt256.ofNat 1168 := by decide
@[simp] private theorem next571 : (UInt256.ofNat 1168).succ = UInt256.ofNat 1169 := by decide
@[simp] private theorem next572 : (UInt256.ofNat 1169).succ = UInt256.ofNat 1170 := by decide
@[simp] private theorem next573 : (UInt256.ofNat 1170).succ = UInt256.ofNat 1171 := by decide
@[simp] private theorem next574 : (UInt256.ofNat 1171).succ = UInt256.ofNat 1172 := by decide
@[simp] private theorem next575 : UInt256.ofNat 1172 + UInt256.ofNat 2 = UInt256.ofNat 1174 := by decide
@[simp] private theorem next576 : UInt256.ofNat 1174 + UInt256.ofNat 5 = UInt256.ofNat 1179 := by decide
@[simp] private theorem next577 : (UInt256.ofNat 1179).succ = UInt256.ofNat 1180 := by decide
@[simp] private theorem next578 : UInt256.ofNat 1180 + UInt256.ofNat 2 = UInt256.ofNat 1182 := by decide
@[simp] private theorem next579 : (UInt256.ofNat 1182).succ = UInt256.ofNat 1183 := by decide
@[simp] private theorem next580 : (UInt256.ofNat 1183).succ = UInt256.ofNat 1184 := by decide
@[simp] private theorem next581 : (UInt256.ofNat 1184).succ = UInt256.ofNat 1185 := by decide
@[simp] private theorem next582 : (UInt256.ofNat 1185).succ = UInt256.ofNat 1186 := by decide
@[simp] private theorem next583 : (UInt256.ofNat 1186).succ = UInt256.ofNat 1187 := by decide
@[simp] private theorem next584 : (UInt256.ofNat 1187).succ = UInt256.ofNat 1188 := by decide
@[simp] private theorem next585 : (UInt256.ofNat 1188).succ = UInt256.ofNat 1189 := by decide
@[simp] private theorem next586 : (UInt256.ofNat 1189).succ = UInt256.ofNat 1190 := by decide
@[simp] private theorem next587 : (UInt256.ofNat 1190).succ = UInt256.ofNat 1191 := by decide
@[simp] private theorem next588 : (UInt256.ofNat 1191).succ = UInt256.ofNat 1192 := by decide
@[simp] private theorem next782 : UInt256.ofNat 1508 + UInt256.ofNat 5 = UInt256.ofNat 1513 := by decide
@[simp] private theorem next783 : (UInt256.ofNat 1513).succ = UInt256.ofNat 1514 := by decide
@[simp] private theorem next784 : UInt256.ofNat 1514 + UInt256.ofNat 2 = UInt256.ofNat 1516 := by decide
@[simp] private theorem next785 : (UInt256.ofNat 1516).succ = UInt256.ofNat 1517 := by decide
@[simp] private theorem next786 : (UInt256.ofNat 1517).succ = UInt256.ofNat 1518 := by decide
@[simp] private theorem next787 : (UInt256.ofNat 1518).succ = UInt256.ofNat 1519 := by decide
@[simp] private theorem next788 : (UInt256.ofNat 1519).succ = UInt256.ofNat 1520 := by decide
@[simp] private theorem next789 : (UInt256.ofNat 1520).succ = UInt256.ofNat 1521 := by decide
@[simp] private theorem next790 : (UInt256.ofNat 1521).succ = UInt256.ofNat 1522 := by decide
@[simp] private theorem next791 : (UInt256.ofNat 1522).succ = UInt256.ofNat 1523 := by decide
@[simp] private theorem next792 : (UInt256.ofNat 1523).succ = UInt256.ofNat 1524 := by decide
@[simp] private theorem next793 : UInt256.ofNat 1524 + UInt256.ofNat 2 = UInt256.ofNat 1526 := by decide
@[simp] private theorem next794 : UInt256.ofNat 1526 + UInt256.ofNat 5 = UInt256.ofNat 1531 := by decide
@[simp] private theorem next795 : (UInt256.ofNat 1531).succ = UInt256.ofNat 1532 := by decide
@[simp] private theorem next796 : UInt256.ofNat 1532 + UInt256.ofNat 2 = UInt256.ofNat 1534 := by decide
@[simp] private theorem next797 : (UInt256.ofNat 1534).succ = UInt256.ofNat 1535 := by decide
@[simp] private theorem next798 : (UInt256.ofNat 1535).succ = UInt256.ofNat 1536 := by decide
@[simp] private theorem next799 : (UInt256.ofNat 1536).succ = UInt256.ofNat 1537 := by decide
@[simp] private theorem next800 : (UInt256.ofNat 1537).succ = UInt256.ofNat 1538 := by decide
@[simp] private theorem next801 : (UInt256.ofNat 1538).succ = UInt256.ofNat 1539 := by decide
@[simp] private theorem next802 : (UInt256.ofNat 1539).succ = UInt256.ofNat 1540 := by decide
@[simp] private theorem next803 : (UInt256.ofNat 1540).succ = UInt256.ofNat 1541 := by decide
@[simp] private theorem next804 : (UInt256.ofNat 1541).succ = UInt256.ofNat 1542 := by decide
@[simp] private theorem next805 : (UInt256.ofNat 1542).succ = UInt256.ofNat 1543 := by decide
@[simp] private theorem next806 : (UInt256.ofNat 1543).succ = UInt256.ofNat 1544 := by decide
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

/-- Inlined 32-bit rotate-right at instruction 237: right shift by the count on
top of the stack, OR left shift by the literal complement 0x7, truncated to
32 bits.  Shape A — the rotated word stays on the stack beneath the result. -/
def rotrPath237 :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨237, .push ⟨4, by decide⟩ (UInt256.ofNat 4294967295), by rfl, by decide⟩,
   ⟨238, .op (.Dup ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨239, .push ⟨1, by decide⟩ (UInt256.ofNat 7), by rfl, by decide⟩,
   ⟨240, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨241, .op (.Dup ⟨5, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨242, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨243, .op (.Swap ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨244, .op (.Swap ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨245, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨246, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨247, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩]

def rotrEntry237 (s : State) (count w1 w2 w3 : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat (Artifact.referenceArtifact.instructionPC 237)
    stack := count :: w1 :: w2 :: w3 :: rest }

def rotrResult237 (s : State) (count w1 w2 w3 : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat (Artifact.referenceArtifact.instructionPC 248)
    stack := maskedRotr w3 count 7 :: w1 :: w2 :: w3 :: rest }

set_option maxHeartbeats 1000000 in
theorem run_rotr237 (s : State) (count w1 w2 w3 : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock rotrPath237
      (rotrEntry237 s count w1 w2 w3 rest) =
        some (rotrResult237 s count w1 w2 w3 rest) := by
  have h4 : rest.length + 1 + 1 + 1 + 1 < 1024 := by omega
  have h5 : rest.length + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h6 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h7 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  simp [rotrPath237, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    rotrEntry237, rotrResult237, maskedRotr, List.exchange,
    h4, h5, h6, h7, hrun]

/-- Inlined 32-bit rotate-right at instruction 249: right shift by the count on
top of the stack, OR left shift by the literal complement 0x15, truncated to
32 bits.  Shape A — the rotated word stays on the stack beneath the result. -/
def rotrPath249 :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨249, .push ⟨4, by decide⟩ (UInt256.ofNat 4294967295), by rfl, by decide⟩,
   ⟨250, .op (.Dup ⟨5, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨251, .push ⟨1, by decide⟩ (UInt256.ofNat 21), by rfl, by decide⟩,
   ⟨252, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨253, .op (.Dup ⟨6, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨254, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨255, .op (.Swap ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨256, .op (.Swap ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨257, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨258, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨259, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩]

def rotrEntry249 (s : State) (count w1 w2 w3 w4 : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat (Artifact.referenceArtifact.instructionPC 249)
    stack := count :: w1 :: w2 :: w3 :: w4 :: rest }

def rotrResult249 (s : State) (count w1 w2 w3 w4 : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat (Artifact.referenceArtifact.instructionPC 260)
    stack := maskedRotr w4 count 21 :: w1 :: w2 :: w3 :: w4 :: rest }

set_option maxHeartbeats 1000000 in
theorem run_rotr249 (s : State) (count w1 w2 w3 w4 : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock rotrPath249
      (rotrEntry249 s count w1 w2 w3 w4 rest) =
        some (rotrResult249 s count w1 w2 w3 w4 rest) := by
  have h5 : rest.length + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h6 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h7 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h8 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  simp [rotrPath249, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    rotrEntry249, rotrResult249, maskedRotr, List.exchange,
    h5, h6, h7, h8, hrun]

/-- Inlined 32-bit rotate-right at instruction 261: right shift by the count on
top of the stack, OR left shift by the literal complement 0x1a, truncated to
32 bits.  Shape A — the rotated word stays on the stack beneath the result. -/
def rotrPath261 :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨261, .push ⟨4, by decide⟩ (UInt256.ofNat 4294967295), by rfl, by decide⟩,
   ⟨262, .op (.Dup ⟨6, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨263, .push ⟨1, by decide⟩ (UInt256.ofNat 26), by rfl, by decide⟩,
   ⟨264, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨265, .op (.Dup ⟨7, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨266, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨267, .op (.Swap ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨268, .op (.Swap ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨269, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨270, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨271, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩]

def rotrEntry261 (s : State) (count w1 w2 w3 w4 w5 : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat (Artifact.referenceArtifact.instructionPC 261)
    stack := count :: w1 :: w2 :: w3 :: w4 :: w5 :: rest }

def rotrResult261 (s : State) (count w1 w2 w3 w4 w5 : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat (Artifact.referenceArtifact.instructionPC 272)
    stack := maskedRotr w5 count 26 :: w1 :: w2 :: w3 :: w4 :: w5 :: rest }

set_option maxHeartbeats 1000000 in
theorem run_rotr261 (s : State) (count w1 w2 w3 w4 w5 : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock rotrPath261
      (rotrEntry261 s count w1 w2 w3 w4 w5 rest) =
        some (rotrResult261 s count w1 w2 w3 w4 w5 rest) := by
  have h6 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h7 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h8 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h9 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  simp [rotrPath261, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    rotrEntry261, rotrResult261, maskedRotr, List.exchange,
    h6, h7, h8, h9, hrun]

/-- Inlined 32-bit rotate-right at instruction 564: right shift by the count on
top of the stack, OR left shift by the literal complement 0xe, truncated to
32 bits.  Shape A — the rotated word stays on the stack beneath the result. -/
def rotrPath564 :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨564, .push ⟨4, by decide⟩ (UInt256.ofNat 4294967295), by rfl, by decide⟩,
   ⟨565, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨566, .push ⟨1, by decide⟩ (UInt256.ofNat 14), by rfl, by decide⟩,
   ⟨567, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨568, .op (.Dup ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨569, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨570, .op (.Swap ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨571, .op (.Swap ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨572, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨573, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨574, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩]

def rotrEntry564 (s : State) (count w1 w2 : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat (Artifact.referenceArtifact.instructionPC 564)
    stack := count :: w1 :: w2 :: rest }

def rotrResult564 (s : State) (count w1 w2 : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat (Artifact.referenceArtifact.instructionPC 575)
    stack := maskedRotr w2 count 14 :: w1 :: w2 :: rest }

set_option maxHeartbeats 1000000 in
theorem run_rotr564 (s : State) (count w1 w2 : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock rotrPath564
      (rotrEntry564 s count w1 w2 rest) =
        some (rotrResult564 s count w1 w2 rest) := by
  have h3 : rest.length + 1 + 1 + 1 < 1024 := by omega
  have h4 : rest.length + 1 + 1 + 1 + 1 < 1024 := by omega
  have h5 : rest.length + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h6 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  simp [rotrPath564, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    rotrEntry564, rotrResult564, maskedRotr, List.exchange,
    h3, h4, h5, h6, hrun]

/-- Inlined 32-bit rotate-right at instruction 782: right shift by the count on
top of the stack, OR left shift by the literal complement 0xd, truncated to
32 bits.  Shape A — the rotated word stays on the stack beneath the result. -/
def rotrPath782 :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨782, .push ⟨4, by decide⟩ (UInt256.ofNat 4294967295), by rfl, by decide⟩,
   ⟨783, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨784, .push ⟨1, by decide⟩ (UInt256.ofNat 13), by rfl, by decide⟩,
   ⟨785, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨786, .op (.Dup ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨787, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨788, .op (.Swap ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨789, .op (.Swap ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨790, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨791, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨792, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩]

def rotrEntry782 (s : State) (count w1 w2 : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat (Artifact.referenceArtifact.instructionPC 782)
    stack := count :: w1 :: w2 :: rest }

def rotrResult782 (s : State) (count w1 w2 : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat (Artifact.referenceArtifact.instructionPC 793)
    stack := maskedRotr w2 count 13 :: w1 :: w2 :: rest }

set_option maxHeartbeats 1000000 in
theorem run_rotr782 (s : State) (count w1 w2 : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock rotrPath782
      (rotrEntry782 s count w1 w2 rest) =
        some (rotrResult782 s count w1 w2 rest) := by
  have h3 : rest.length + 1 + 1 + 1 < 1024 := by omega
  have h4 : rest.length + 1 + 1 + 1 + 1 < 1024 := by omega
  have h5 : rest.length + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h6 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  simp [rotrPath782, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    rotrEntry782, rotrResult782, maskedRotr, List.exchange,
    h3, h4, h5, h6, hrun]

/-- Inlined 32-bit rotate-right at instruction 829: right shift by the count on
top of the stack, OR left shift by the literal complement 0xa, truncated to
32 bits.  Shape A — the rotated word stays on the stack beneath the result. -/
def rotrPath829 :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨829, .push ⟨4, by decide⟩ (UInt256.ofNat 4294967295), by rfl, by decide⟩,
   ⟨830, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨831, .push ⟨1, by decide⟩ (UInt256.ofNat 10), by rfl, by decide⟩,
   ⟨832, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨833, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨834, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨835, .op (.Swap ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨836, .op (.Swap ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨837, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨838, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨839, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩]

def rotrEntry829 (s : State) (count w1 : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat (Artifact.referenceArtifact.instructionPC 829)
    stack := count :: w1 :: rest }

def rotrResult829 (s : State) (count w1 : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat (Artifact.referenceArtifact.instructionPC 840)
    stack := maskedRotr w1 count 10 :: w1 :: rest }

set_option maxHeartbeats 1000000 in
theorem run_rotr829 (s : State) (count w1 : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock rotrPath829
      (rotrEntry829 s count w1 rest) =
        some (rotrResult829 s count w1 rest) := by
  have h2 : rest.length + 1 + 1 < 1024 := by omega
  have h3 : rest.length + 1 + 1 + 1 < 1024 := by omega
  have h4 : rest.length + 1 + 1 + 1 + 1 < 1024 := by omega
  have h5 : rest.length + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  simp [rotrPath829, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    rotrEntry829, rotrResult829, maskedRotr, List.exchange,
    h2, h3, h4, h5, hrun]

/-- Inlined 32-bit rotate-right at instruction 841: right shift by the count on
top of the stack, OR left shift by the literal complement 0x13, truncated to
32 bits.  Shape A — the rotated word stays on the stack beneath the result. -/
def rotrPath841 :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨841, .push ⟨4, by decide⟩ (UInt256.ofNat 4294967295), by rfl, by decide⟩,
   ⟨842, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨843, .push ⟨1, by decide⟩ (UInt256.ofNat 19), by rfl, by decide⟩,
   ⟨844, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨845, .op (.Dup ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨846, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨847, .op (.Swap ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨848, .op (.Swap ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨849, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨850, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨851, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩]

def rotrEntry841 (s : State) (count w1 w2 : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat (Artifact.referenceArtifact.instructionPC 841)
    stack := count :: w1 :: w2 :: rest }

def rotrResult841 (s : State) (count w1 w2 : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat (Artifact.referenceArtifact.instructionPC 852)
    stack := maskedRotr w2 count 19 :: w1 :: w2 :: rest }

set_option maxHeartbeats 1000000 in
theorem run_rotr841 (s : State) (count w1 w2 : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock rotrPath841
      (rotrEntry841 s count w1 w2 rest) =
        some (rotrResult841 s count w1 w2 rest) := by
  have h3 : rest.length + 1 + 1 + 1 < 1024 := by omega
  have h4 : rest.length + 1 + 1 + 1 + 1 < 1024 := by omega
  have h5 : rest.length + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h6 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  simp [rotrPath841, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    rotrEntry841, rotrResult841, maskedRotr, List.exchange,
    h3, h4, h5, h6, hrun]

/-- Inlined 32-bit rotate-right at instruction 576: right shift by the count on
top of the stack, OR left shift by the literal complement 0x19, truncated to
32 bits.  Shape B — this shape consumes `w3` as well as the count. -/
def rotrPath576 :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨576, .push ⟨4, by decide⟩ (UInt256.ofNat 4294967295), by rfl, by decide⟩,
   ⟨577, .op (.Dup ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨578, .push ⟨1, by decide⟩ (UInt256.ofNat 25), by rfl, by decide⟩,
   ⟨579, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨580, .op (.Swap ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨581, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨582, .op (.Swap ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨583, .op (.Swap ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨584, .op (.Swap ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨585, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨586, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨587, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨588, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩]

def rotrEntry576 (s : State) (count w1 w2 w3 : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat (Artifact.referenceArtifact.instructionPC 576)
    stack := count :: w1 :: w2 :: w3 :: rest }

def rotrResult576 (s : State) (count w1 w2 w3 : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat (Artifact.referenceArtifact.instructionPC 589)
    stack := maskedRotr w3 count 25 :: w1 :: w2 :: rest }

set_option maxHeartbeats 1000000 in
theorem run_rotr576 (s : State) (count w1 w2 w3 : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock rotrPath576
      (rotrEntry576 s count w1 w2 w3 rest) =
        some (rotrResult576 s count w1 w2 w3 rest) := by
  have h4 : rest.length + 1 + 1 + 1 + 1 < 1024 := by omega
  have h5 : rest.length + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h6 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h7 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  simp [rotrPath576, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    rotrEntry576, rotrResult576, maskedRotr, List.exchange,
    h4, h5, h6, h7, hrun]

/-- Inlined 32-bit rotate-right at instruction 794: right shift by the count on
top of the stack, OR left shift by the literal complement 0xf, truncated to
32 bits.  Shape B — this shape consumes `w3` as well as the count. -/
def rotrPath794 :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨794, .push ⟨4, by decide⟩ (UInt256.ofNat 4294967295), by rfl, by decide⟩,
   ⟨795, .op (.Dup ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨796, .push ⟨1, by decide⟩ (UInt256.ofNat 15), by rfl, by decide⟩,
   ⟨797, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨798, .op (.Swap ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨799, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨800, .op (.Swap ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨801, .op (.Swap ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨802, .op (.Swap ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨803, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨804, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨805, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨806, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩]

def rotrEntry794 (s : State) (count w1 w2 w3 : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat (Artifact.referenceArtifact.instructionPC 794)
    stack := count :: w1 :: w2 :: w3 :: rest }

def rotrResult794 (s : State) (count w1 w2 w3 : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat (Artifact.referenceArtifact.instructionPC 807)
    stack := maskedRotr w3 count 15 :: w1 :: w2 :: rest }

set_option maxHeartbeats 1000000 in
theorem run_rotr794 (s : State) (count w1 w2 w3 : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock rotrPath794
      (rotrEntry794 s count w1 w2 w3 rest) =
        some (rotrResult794 s count w1 w2 w3 rest) := by
  have h4 : rest.length + 1 + 1 + 1 + 1 < 1024 := by omega
  have h5 : rest.length + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h6 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h7 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  simp [rotrPath794, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    rotrEntry794, rotrResult794, maskedRotr, List.exchange,
    h4, h5, h6, h7, hrun]

/-- Inlined 32-bit rotate-right at instruction 853: right shift by the count on
top of the stack, OR left shift by the literal complement 0x1e, truncated to
32 bits.  Shape B — this shape consumes `w3` as well as the count. -/
def rotrPath853 :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨853, .push ⟨4, by decide⟩ (UInt256.ofNat 4294967295), by rfl, by decide⟩,
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
   ⟨865, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩]

def rotrEntry853 (s : State) (count w1 w2 w3 : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat (Artifact.referenceArtifact.instructionPC 853)
    stack := count :: w1 :: w2 :: w3 :: rest }

def rotrResult853 (s : State) (count w1 w2 w3 : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat (Artifact.referenceArtifact.instructionPC 866)
    stack := maskedRotr w3 count 30 :: w1 :: w2 :: rest }

set_option maxHeartbeats 1000000 in
theorem run_rotr853 (s : State) (count w1 w2 w3 : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock rotrPath853
      (rotrEntry853 s count w1 w2 w3 rest) =
        some (rotrResult853 s count w1 w2 w3 rest) := by
  have h4 : rest.length + 1 + 1 + 1 + 1 < 1024 := by omega
  have h5 : rest.length + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h6 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h7 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  simp [rotrPath853, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    rotrEntry853, rotrResult853, maskedRotr, List.exchange,
    h4, h5, h6, h7, hrun]

/-! ### The schedule's small sigma-1

Unlike `rotr`, this one is still a called function: entry `JUMPDEST` at 777,
returning `JUMP` at 810, on the frame `[x, returnAddress]`.  Its two rotations
are the inlined sites 782 and 794 certified above, and it finishes with a plain
right shift rather than a third rotation:

  smallSigma1 x = rotr x 17 ^^^ rotr x 19 ^^^ (x >>> 10)
-/

def smallSigma1Word (x : UInt256) : UInt256 :=
  UInt256.xor
    (UInt256.xor (maskedRotr x (UInt256.ofNat 17) 0xf)
      (maskedRotr x (UInt256.ofNat 19) 0xd))
    (UInt256.shiftRight x (UInt256.ofNat 10))

@[simp] private theorem pc777 :
    Artifact.referenceArtifact.instructionPC 777 = 1501 := by decide

@[simp] private theorem pc778 :
    Artifact.referenceArtifact.instructionPC 778 = 1502 := by decide

@[simp] private theorem pc779 :
    Artifact.referenceArtifact.instructionPC 779 = 1503 := by decide

@[simp] private theorem pc780 :
    Artifact.referenceArtifact.instructionPC 780 = 1505 := by decide

@[simp] private theorem pc781 :
    Artifact.referenceArtifact.instructionPC 781 = 1506 := by decide

@[simp] private theorem pc808 :
    Artifact.referenceArtifact.instructionPC 808 = 1545 := by decide

@[simp] private theorem pc809 :
    Artifact.referenceArtifact.instructionPC 809 = 1546 := by decide

@[simp] private theorem pc810 :
    Artifact.referenceArtifact.instructionPC 810 = 1547 := by decide

@[simp] private theorem pc811 :
    Artifact.referenceArtifact.instructionPC 811 = 1548 := by decide

@[simp] private theorem toNat1501 : (UInt256.ofNat 1501).toNat = 1501 := by decide
@[simp] private theorem toNat1502 : (UInt256.ofNat 1502).toNat = 1502 := by decide
@[simp] private theorem toNat1503 : (UInt256.ofNat 1503).toNat = 1503 := by decide
@[simp] private theorem toNat1505 : (UInt256.ofNat 1505).toNat = 1505 := by decide
@[simp] private theorem toNat1506 : (UInt256.ofNat 1506).toNat = 1506 := by decide
@[simp] private theorem toNat1545 : (UInt256.ofNat 1545).toNat = 1545 := by decide
@[simp] private theorem toNat1546 : (UInt256.ofNat 1546).toNat = 1546 := by decide
@[simp] private theorem toNat1547 : (UInt256.ofNat 1547).toNat = 1547 := by decide
@[simp] private theorem toNat1548 : (UInt256.ofNat 1548).toNat = 1548 := by decide

@[simp] private theorem next777 : (UInt256.ofNat 1501).succ = UInt256.ofNat 1502 := by decide
@[simp] private theorem next778 : (UInt256.ofNat 1502).succ = UInt256.ofNat 1503 := by decide
@[simp] private theorem next779 : UInt256.ofNat 1503 + UInt256.ofNat 2 = UInt256.ofNat 1505 := by decide
@[simp] private theorem next780 : (UInt256.ofNat 1505).succ = UInt256.ofNat 1506 := by decide
@[simp] private theorem next781 : UInt256.ofNat 1506 + UInt256.ofNat 2 = UInt256.ofNat 1508 := by decide
@[simp] private theorem next807 : (UInt256.ofNat 1544).succ = UInt256.ofNat 1545 := by decide
@[simp] private theorem next808 : (UInt256.ofNat 1545).succ = UInt256.ofNat 1546 := by decide
@[simp] private theorem next809 : (UInt256.ofNat 1546).succ = UInt256.ofNat 1547 := by decide
@[simp] private theorem next810 : (UInt256.ofNat 1547).succ = UInt256.ofNat 1548 := by decide

def smallSigma1Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨777, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨778, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨779, .push ⟨1, by decide⟩ (UInt256.ofNat 10), by rfl, by decide⟩,
   ⟨780, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨781, .push ⟨1, by decide⟩ (UInt256.ofNat 19), by rfl, by decide⟩,
   ⟨782, .push ⟨4, by decide⟩ (UInt256.ofNat 4294967295), by rfl, by decide⟩,
   ⟨783, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨784, .push ⟨1, by decide⟩ (UInt256.ofNat 13), by rfl, by decide⟩,
   ⟨785, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨786, .op (.Dup ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨787, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨788, .op (.Swap ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨789, .op (.Swap ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨790, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨791, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨792, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨793, .push ⟨1, by decide⟩ (UInt256.ofNat 17), by rfl, by decide⟩,
   ⟨794, .push ⟨4, by decide⟩ (UInt256.ofNat 4294967295), by rfl, by decide⟩,
   ⟨795, .op (.Dup ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨796, .push ⟨1, by decide⟩ (UInt256.ofNat 15), by rfl, by decide⟩,
   ⟨797, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨798, .op (.Swap ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨799, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨800, .op (.Swap ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨801, .op (.Swap ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨802, .op (.Swap ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨803, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨804, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨805, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨806, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨807, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨808, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨809, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨810, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def smallSigma1Entry (s : State) (x returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat (Artifact.referenceArtifact.instructionPC 777)
    stack := x :: returnDest :: rest }

def smallSigma1Returned (s : State) (x returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := returnDest
    stack := smallSigma1Word x :: rest }

set_option maxHeartbeats 4000000 in
theorem run_smallSigma1 (s : State) (x returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000) (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true)
    (hcode : s.executionEnv.code = referenceBytecode) :
    Challenge.EvmProof.Stepper.runLocatedBlock smallSigma1Path
      (smallSigma1Entry s x returnDest rest) =
        some (smallSigma1Returned s x returnDest rest) := by
  have g2 : rest.length + 1 + 1 < 1024 := by omega
  have g3 : rest.length + 1 + 1 + 1 < 1024 := by omega
  have g4 : rest.length + 1 + 1 + 1 + 1 < 1024 := by omega
  have g5 : rest.length + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have g6 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have g7 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have g8 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  simp [smallSigma1Path, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    smallSigma1Entry, smallSigma1Returned, smallSigma1Word, maskedRotr,
    List.exchange, g2, g3, g4, g5, g6, g7, g8, hrun, hvalid, hcode]

/-! ### The schedule's small sigma-0, inlined

The backend inlined this one — unlike `smallSigma1`, there is no function to
call.  It occupies instructions 560..590 inside the extension loop's body and
replaces the word on top of the stack with its sigma-0:

  smallSigma0 x = rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
-/

def smallSigma0Word (x : UInt256) : UInt256 :=
  UInt256.xor
    (UInt256.xor (maskedRotr x (UInt256.ofNat 7) 0x19)
      (maskedRotr x (UInt256.ofNat 18) 0xe))
    (UInt256.shiftRight x (UInt256.ofNat 3))

@[simp] private theorem pc560 :
    Artifact.referenceArtifact.instructionPC 560 = 1150 := by decide

@[simp] private theorem pc561 :
    Artifact.referenceArtifact.instructionPC 561 = 1151 := by decide

@[simp] private theorem pc562 :
    Artifact.referenceArtifact.instructionPC 562 = 1153 := by decide

@[simp] private theorem pc563 :
    Artifact.referenceArtifact.instructionPC 563 = 1154 := by decide

@[simp] private theorem pc590 :
    Artifact.referenceArtifact.instructionPC 590 = 1193 := by decide

@[simp] private theorem pc591 :
    Artifact.referenceArtifact.instructionPC 591 = 1194 := by decide

@[simp] private theorem toNat1150 : (UInt256.ofNat 1150).toNat = 1150 := by decide
@[simp] private theorem toNat1151 : (UInt256.ofNat 1151).toNat = 1151 := by decide
@[simp] private theorem toNat1153 : (UInt256.ofNat 1153).toNat = 1153 := by decide
@[simp] private theorem toNat1154 : (UInt256.ofNat 1154).toNat = 1154 := by decide
@[simp] private theorem toNat1193 : (UInt256.ofNat 1193).toNat = 1193 := by decide
@[simp] private theorem toNat1194 : (UInt256.ofNat 1194).toNat = 1194 := by decide

@[simp] private theorem next560 : (UInt256.ofNat 1150).succ = UInt256.ofNat 1151 := by decide
@[simp] private theorem next561 : UInt256.ofNat 1151 + UInt256.ofNat 2 = UInt256.ofNat 1153 := by decide
@[simp] private theorem next562 : (UInt256.ofNat 1153).succ = UInt256.ofNat 1154 := by decide
@[simp] private theorem next563 : UInt256.ofNat 1154 + UInt256.ofNat 2 = UInt256.ofNat 1156 := by decide
@[simp] private theorem next589 : (UInt256.ofNat 1192).succ = UInt256.ofNat 1193 := by decide
@[simp] private theorem next590 : (UInt256.ofNat 1193).succ = UInt256.ofNat 1194 := by decide

def smallSigma0Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨560, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨561, .push ⟨1, by decide⟩ (UInt256.ofNat 3), by rfl, by decide⟩,
   ⟨562, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨563, .push ⟨1, by decide⟩ (UInt256.ofNat 18), by rfl, by decide⟩,
   ⟨564, .push ⟨4, by decide⟩ (UInt256.ofNat 4294967295), by rfl, by decide⟩,
   ⟨565, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨566, .push ⟨1, by decide⟩ (UInt256.ofNat 14), by rfl, by decide⟩,
   ⟨567, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨568, .op (.Dup ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨569, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨570, .op (.Swap ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨571, .op (.Swap ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨572, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨573, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨574, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨575, .push ⟨1, by decide⟩ (UInt256.ofNat 7), by rfl, by decide⟩,
   ⟨576, .push ⟨4, by decide⟩ (UInt256.ofNat 4294967295), by rfl, by decide⟩,
   ⟨577, .op (.Dup ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨578, .push ⟨1, by decide⟩ (UInt256.ofNat 25), by rfl, by decide⟩,
   ⟨579, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨580, .op (.Swap ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨581, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨582, .op (.Swap ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨583, .op (.Swap ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨584, .op (.Swap ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨585, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨586, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨587, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨588, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨589, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨590, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩]

def smallSigma0Entry (s : State) (x other : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat (Artifact.referenceArtifact.instructionPC 560)
    stack := x :: other :: rest }

def smallSigma0Result (s : State) (x other : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat (Artifact.referenceArtifact.instructionPC 591)
    stack := smallSigma0Word x :: other :: rest }

set_option maxHeartbeats 4000000 in
theorem run_smallSigma0 (s : State) (x other : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock smallSigma0Path
      (smallSigma0Entry s x other rest) =
        some (smallSigma0Result s x other rest) := by
  have q2 : rest.length + 1 + 1 < 1024 := by omega
  have q3 : rest.length + 1 + 1 + 1 < 1024 := by omega
  have q4 : rest.length + 1 + 1 + 1 + 1 < 1024 := by omega
  have q5 : rest.length + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have q6 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have q7 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have q8 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  simp [smallSigma0Path, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    smallSigma0Entry, smallSigma0Result, smallSigma0Word, maskedRotr,
    List.exchange, q2, q3, q4, q5, q6, q7, q8, hrun]

end Challenge.Sha256.Reference.Proofs.Bytecode.Functions
