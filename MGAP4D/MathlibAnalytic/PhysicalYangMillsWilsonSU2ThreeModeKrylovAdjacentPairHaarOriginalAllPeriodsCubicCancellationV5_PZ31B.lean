import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalMinimalPeriodParityV5_PZ31
import Mathlib.Tactic

/-!
# P4-Q2-PZ31B — original SU(2) three-plaquette Haar cancellation on ALL periods

PZ31 (merged #5895) establishes the exact kernel-checked period-two
H=0 triple-plaquette odd-link lower bound |Odd(p,q,r)| >= 4. PZ30
establishes |Odd(p,q,r)| >= 6 for all H >= 1.

This file TRANSPORTS those already proved original physical geometry
theorems to the genuine SU(2) center-flip Haar selection of PZ27:
for any finite even periodic side 2*(H+1), each original ordered
triple of pairwise distinct spatial plaquettes has > 2 odd spatial
links. Thus no pair of actual temporal crossing links can cover them.

The original triple Haar integral, PZ29's full residual finite sum,
Z32, and the boundary-normalized D32 vanish on EVERY finite even
period, including H=0. Both actual posterior sectors, genuine spatial
Haar, original SU(2) Wilson action, intermediate spatial plaquettes,
Gauss-law source, and temporal Wilson interactions are unchanged.

Crucially, the expensive verified H=0 finite proof is IMPORTED, not
duplicated via a second gigantic \`fin_cases p <;> decide\` evaluation.
No native_decide, surrogate, new axiom, sorry, admit, third Hankel,
rank-3 assertion or continuum mass-gap claim.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ31B_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex H)
    PeriodicHypercubicEvenSpatialDirection
local instance p4Q2PZ31B_plaqFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSlicePlaquette H) :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex H)
    PeriodicHypercubicEvenSpatialDirectionPair

namespace GroundStatePosteriorJoint
section OriginalAllPeriodsCubicCancellation

local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration
local notation "OddSet" => p4Q2PZ28_originalOddEdges
local notation "Adm" => p4Q2PZ27_originalTwoLinkCoversOddEdges
local notation "J2" => p4Q2PZ26_originalTriplePlaquetteTwoLinkHaar
local notation "Selected2" =>
  p4Q2PZ27_originalParityAdmissibleTripleTwoLinkHaar
local notation "Residual3" => p4Q2PZ29_originalNonThinGeometricHaar
local notation "Z32" => p4Q2PZ24_originalCenteredCubeCrossSquareHaar
local notation "D32" => p4Q2PZ24_originalCenteredCubeSquareDefect

/-- Genuine spatial odd-incidence links of a pairwise-distinct
triple number at least four on EVERY finite even period. The H=0
case reuses the kernel-checked PZ31 result; H>=1 uses PZ30. -/
theorem p4Q2PZ31B_originalAllPeriodsTripleOddEdges_card_ge_four
    (H : ℕ) (p q r : Plaq H)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    4 ≤ (OddSet H p q r).card := by
  cases H with
  | zero =>
      exact p4Q2PZ31_originalMinimalTripleOddEdges_card_ge_four
        p q r hpq hpr hqr
  | succ n =>
      have hPos : 1 ≤ n + 1 := by omega
      have hSix :=
        p4Q2PZ30_originalTripleOddEdges_card_ge_six
          (n + 1) hPos p q r hpq hpr hqr
      omega

/-- Two genuinely crossed temporal Wilson links cannot cover
all odd spatial edges of any three distinct original plaquettes. -/
theorem p4Q2PZ31B_originalAllPeriodsTripleTwoLinks_notCover
    (H : ℕ) (p q r : Plaq H)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (e f : Link H) :
    ¬ Adm H p q r e f := by
  intro hAdm
  have hFour :=
    p4Q2PZ31B_originalAllPeriodsTripleOddEdges_card_ge_four
      H p q r hpq hpr hqr
  have hTwo :=
    p4Q2PZ29_originalOddEdges_card_le_two_of_covered
      H p q r e f hAdm
  omega

/-- Genuine original SU(2) Haar selection, retaining the full
crossing energies, spatial intermediate Wilson weights, and Haar. -/
theorem p4Q2PZ31B_originalAllPeriodsTripleTwoLinkHaar_zero
    (H : ℕ) (p q r : Plaq H)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (e f : Link H) (B : Cfg H 2) :
    J2 H p q r e f B = 0 :=
  p4Q2PZ27_originalTripleTwoLinkHaar_zero_of_notAdmissible
    H p q r e f B
    (p4Q2PZ31B_originalAllPeriodsTripleTwoLinks_notCover
      H p q r hpq hpr hqr e f)

/-- Exact sum over ALL ordered genuine temporal Wilson crossing
link pairs, not a modified interaction or a factored posterior. -/
theorem p4Q2PZ31B_originalAllPeriodsSelectedTwoLinkHaar_zero
    (H : ℕ) (p q r : Plaq H)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (B : Cfg H 2) :
    Selected2 H p q r B = 0 := by
  classical
  unfold p4Q2PZ27_originalParityAdmissibleTripleTwoLinkHaar
  apply Finset.sum_eq_zero
  intro e _he
  apply Finset.sum_eq_zero
  intro f _hf
  have hNot :=
    p4Q2PZ31B_originalAllPeriodsTripleTwoLinks_notCover
      H p q r hpq hpr hqr e f
  simp [hNot]

/-- PZ29's entire original triple-spatial-plaquette finite Haar
residual, with only PROVED zero terms removed, is identically zero. -/
theorem p4Q2PZ31B_originalAllPeriodsResidualTripleHaar_zero
    (H : ℕ) (B : Cfg H 2) :
    Residual3 H B = 0 := by
  classical
  unfold p4Q2PZ29_originalNonThinGeometricHaar
  apply Finset.sum_eq_zero
  intro p _hp
  apply Finset.sum_eq_zero
  intro q _hq
  apply Finset.sum_eq_zero
  intro r _hr
  by_cases hDistinct : p ≠ q ∧ p ≠ r ∧ q ≠ r
  · obtain ⟨hpq, hpr, hqr⟩ := hDistinct
    have hZero :=
      p4Q2PZ31B_originalAllPeriodsSelectedTwoLinkHaar_zero
        H p q r hpq hpr hqr B
    simp [hpq, hpr, hqr, hZero]
  · have hNot :
        ¬ (p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
          p4Q2PZ28_originalAtLeastTwoSharedPairs H p q r ∧
          ¬ p4Q2PZ29_originalHasSingleJunction H p q r) := by
      rintro ⟨hpq, hpr, hqr, _, _⟩
      exact hDistinct ⟨hpq, hpr, hqr⟩
    simp [hNot]

/-- The ORIGINAL spatial centered-cubic/two-temporal-crossing
Haar contribution vanishes on every finite even period. -/
theorem p4Q2PZ31B_originalAllPeriodsCenteredCube_zero
    (H : ℕ) (B : Cfg H 2) :
    Z32 H B = 0 := by
  rw [p4Q2PZ29_originalCenteredCube_onlyNonThinGeometricTriples H B,
    p4Q2PZ31B_originalAllPeriodsResidualTripleHaar_zero H B]
  ring

/-- The true boundary-normalized D32 contribution to the sixth
Ward obstruction vanishes for ALL finite even spatial periods.
D14, W6 nonzeroness, rank3, third Hankel, and mass gap remain open. -/
theorem p4Q2PZ31B_originalAllPeriodsCenteredCubicDefect_zero
    (H : ℕ) (B : Cfg H 2) :
    D32 H B = 0 := by
  rw [p4Q2PZ29_originalCenteredCubicDefect_onlyNonThinGeometricTriples H B,
    p4Q2PZ31B_originalAllPeriodsResidualTripleHaar_zero H B,
    p4Q2PZ31B_originalAllPeriodsResidualTripleHaar_zero H
      (fun _ : Link H => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ))]
  ring

end OriginalAllPeriodsCubicCancellation
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ31B_originalAllPeriodsTripleOddEdges_card_ge_four
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ31B_originalAllPeriodsTripleTwoLinks_notCover
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ31B_originalAllPeriodsTripleTwoLinkHaar_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ31B_originalAllPeriodsSelectedTwoLinkHaar_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ31B_originalAllPeriodsResidualTripleHaar_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ31B_originalAllPeriodsCenteredCube_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ31B_originalAllPeriodsCenteredCubicDefect_zero
