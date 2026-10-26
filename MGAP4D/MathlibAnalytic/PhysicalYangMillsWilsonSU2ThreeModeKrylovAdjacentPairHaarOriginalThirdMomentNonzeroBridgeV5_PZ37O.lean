import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalRotationalBoundaryWitnessV5_PZ37N
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonThirdMomentPosteriorMassCriterionV5_PE
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonRawTwoSlabLiteralKernelV5_PJ
import Mathlib.Tactic

/-!
# PZ37O — unconditional finite-volume third Wilson moment and physical posterior

PZ37N constructs *actual* SU(2) spatial boundaries whose full one/two-slab
Haar minor is nonzero at sufficiently small positive fine coupling. The
existing original physical D2 pivot (PE) and the proved PJ literal-to-physical
determinant equivalence then give D3 > 0, strictly positive genuine
Gauss-law posterior mass, and a nonzero actual signed two-posterior GI context.

The frozen coupling remains positive and fixed. The fine coupling is positive
and small. Each radius depends on the finite lattice, the chosen contexts,
and the original physical Wilson budget. No volume-uniform, endpoint or
continuum mass-gap statement is made, and the H=0 boundary-loop correction
is not dropped.
-/

namespace MGAP4D.MathlibAnalytic

open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000

namespace GroundStatePosteriorJoint

section OriginalNonminimalThreeModeBridge

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "Pair" => Cfg × Cfg
local notation "D2" =>
  p4Q2PD_originalWilsonTwoMomentDet
    Hn (beta (n + 1)) (hbeta (n + 1))
local notation "D3" =>
  p4Q2PD_originalWilsonThirdMomentGap
    Hn (beta (n + 1)) (hbeta (n + 1))
local notation "S" =>
  p4Q2HJ_actualRightPhysicalSourceSynthesis
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
local notation "a" =>
  p4Q2PE_actualThirdMomentCoefficient
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
local notation "Mass" =>
  p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
    Hn (beta n) (hbeta n)
local notation "Modal" =>
  p4Q2HF_actualRightGIModalLinear
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n

/-- Without a third-rank premise, the authentic physical D2 and D3
determinants are both positive on one finite-volume small-positive-fine
interval. The witness is PZ37N's concrete original SU(2) boundary triple. -/
theorem p4Q2PZ37O_actualSmallFine_twoAndThreeMoments_pos
    (hH : 1 ≤ Hn) (hFrozen : 0 < beta n)
    (e e' : Link) (left₀ right₀ : Cfg) :
    ∃ delta : ℝ, 0 < delta ∧
      (0 < beta (n + 1) → beta (n + 1) < delta →
        0 < D2 ∧ 0 < D3) := by
  obtain ⟨delta₂, hdelta₂, hTwo⟩ :=
    p4Q2PE_actualSmallFine_trueMomentPivot_pos
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e e' left₀ right₀
  obtain ⟨A, B, C, delta₃, hdelta₃, hMinor⟩ :=
    p4Q2PZ37N_originalNonminimalLiteralMinor_exists_nonzero_smallPositive Hn hH
  refine ⟨min delta₂ delta₃, lt_min hdelta₂ hdelta₃, ?_⟩
  intro ht hsmall
  have hSmallTwo : beta (n + 1) < delta₂ :=
    lt_of_lt_of_le hsmall (min_le_left _ _)
  have hSmallMinor : beta (n + 1) < delta₃ :=
    lt_of_lt_of_le hsmall (min_le_right _ _)
  have hD2 : 0 < D2 := hTwo ht hSmallTwo
  have hLiteral :
      p4Q2PJ_originalWilsonLiteralThreeSpatialMinor
        Hn (beta (n + 1)) A B C ≠ 0 :=
    hMinor (beta (n + 1)) ht hSmallMinor
  have hD3 : 0 < D3 :=
    (p4Q2PJ_originalThirdMoment_pos_iff_exists_literalWilsonKernelMinor
      Hn (beta (n + 1)) (hbeta (n + 1)) hD2).mpr
        ⟨A, B, C, hLiteral⟩
  exact ⟨hD2, hD3⟩

/-- The very same genuine original 3x3 physical moment matrix has a
strictly positive determinant on that interval, not just a formal jet
or a conditionally assumed Vandermonde. -/
theorem p4Q2PZ37O_actualSmallFine_originalThreeHankel_det_pos
    (hH : 1 ≤ Hn) (hFrozen : 0 < beta n)
    (e e' : Link) (left₀ right₀ : Cfg) :
    ∃ delta : ℝ, 0 < delta ∧
      (0 < beta (n + 1) → beta (n + 1) < delta →
        0 < (p4Q2PD_originalWilsonThreeHankel
          Hn (beta (n + 1)) (hbeta (n + 1))).det) := by
  obtain ⟨delta, hdelta, hMoments⟩ :=
    p4Q2PZ37O_actualSmallFine_twoAndThreeMoments_pos
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hH hFrozen e e' left₀ right₀
  refine ⟨delta, hdelta, ?_⟩
  intro ht hsmall
  have hThird := (hMoments ht hsmall).2
  rw [p4Q2PD_originalWilsonThreeHankel_det_eq_gap]
  exact hThird

/-- The canonical third moment-Schur source in the original Gauss-law
physical Hilbert carrier has BOTH positive genuine two-posterior GL
mass and a signed two-interacting-Wilson-posterior nonzero GI context.
No independent posterior operator, Haar measure or source is substituted. -/
theorem p4Q2PZ37O_actualSmallFine_originalThirdSource_mass_and_signedGI
    (hH : 1 ≤ Hn) (hFrozen : 0 < beta n)
    (e e' : Link) (left₀ right₀ : Cfg) :
    ∃ delta : ℝ, 0 < delta ∧
      (0 < beta (n + 1) → beta (n + 1) < delta →
        0 < D3 ∧
        0 < Mass (S 2 a) (Finset.univ : Finset Link) ∧
        ∃ z : Pair, Modal 2 e z a ≠ 0) := by
  obtain ⟨delta, hdelta, hMoments⟩ :=
    p4Q2PZ37O_actualSmallFine_twoAndThreeMoments_pos
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hH hFrozen e e' left₀ right₀
  refine ⟨delta, hdelta, ?_⟩
  intro ht hsmall
  obtain ⟨hD2, hD3⟩ := hMoments ht hsmall
  have hMass : 0 < Mass (S 2 a) (Finset.univ : Finset Link) :=
    (p4Q2PE_actualThirdMoment_postMass_pos_iff_thirdGap_pos
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e left₀ hD2).mpr hD3
  have hGI : ∃ z : Pair, Modal 2 e z a ≠ 0 :=
    (p4Q2PE_actualThirdMoment_trueSignedGI_exists_iff_thirdGap_pos
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e left₀ hD2).mpr hD3
  exact ⟨hD3, hMass, hGI⟩

end OriginalNonminimalThreeModeBridge

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37O_actualSmallFine_twoAndThreeMoments_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37O_actualSmallFine_originalThreeHankel_det_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37O_actualSmallFine_originalThirdSource_mass_and_signedGI
