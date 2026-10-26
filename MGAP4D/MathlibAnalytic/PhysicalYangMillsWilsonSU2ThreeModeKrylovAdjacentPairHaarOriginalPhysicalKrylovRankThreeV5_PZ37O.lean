import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalThirdRankPosteriorBridgeV5_PZ37O
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonPhysicalKrylovHankelMomentsV5_PB
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

/-!
# P4-Q2-PZ37O — actual three Gauss-law physical Krylov vectors are independent

The original normalized SU(2) physical Wilson transfer and its genuine
constant Gauss-law unit produce three Hilbert-space vectors U, T U, T² U.
PB proves that their actual Gram matrix is the moment Hankel matrix; PD
identifies its determinant; PZ37O proves that this determinant is strictly
positive in the common small-positive original Wilson coupling interval.

This is *true physical* linear independence, not merely a scalar three-point
evaluation rank, abstract model, substitute kernel, or posterior assumption.
-/

namespace MGAP4D.MathlibAnalytic
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000

namespace GroundStatePosteriorJoint

variable (H : ℕ) (t : ℝ) (ht : 0 ≤ t)
local notation "Phys" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "U" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
local notation "Fine" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive t ht

/-- Strict positivity of the genuine original 3×3 Wilson moment Hankel
determinant implies actual linear independence of the three Gauss-law
physical Hilbert vectors U, T U and T² U. -/
theorem p4Q2PZ37O_originalPhysicalThreeKrylov_linearIndependent_of_det_pos
    (hDet :
      0 < (p4Q2PD_originalWilsonThreeHankel H t ht).det) :
    LinearIndependent ℝ
      (fun j : Fin (2 + 1) => (Fine ^ (j : ℕ)) U) := by
  have hGram :
      Matrix.gram ℝ (fun j : Fin (2 + 1) => (Fine ^ (j : ℕ)) U) =
        p4Q2PD_originalWilsonThreeHankel H t ht :=
    p4Q2PB_originalWilsonPhysicalGram_eq_actualHankel H t ht 2
  have hGramDet :
      (Matrix.gram ℝ
        (fun j : Fin (2 + 1) => (Fine ^ (j : ℕ)) U)).det =
        (p4Q2PD_originalWilsonThreeHankel H t ht).det :=
    congrArg Matrix.det hGram
  have hNonzero :
      (Matrix.gram ℝ
        (fun j : Fin (2 + 1) => (Fine ^ (j : ℕ)) U)).det ≠ 0 := by
    intro hZero
    exact (ne_of_gt hDet) (hGramDet.symm.trans hZero)
  exact Matrix.linearIndependent_of_det_gram_ne_zero hNonzero

/-- The genuine physical moment Hankel matrix has EXACT rank three
under the same certificate; the rank statement uses mathlib's
rank-of-nonzero-determinant theorem, not an extra rank assumption. -/
theorem p4Q2PZ37O_originalPhysicalThreeHankel_rank_three_of_det_pos
    (hDet :
      0 < (p4Q2PD_originalWilsonThreeHankel H t ht).det) :
    (p4Q2PD_originalWilsonThreeHankel H t ht).rank = 3 := by
  have hUnitDet :
      IsUnit (p4Q2PD_originalWilsonThreeHankel H t ht).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hDet)
  have hRank :=
    Matrix.rank_mul_eq_left_of_isUnit_det
      (p4Q2PD_originalWilsonThreeHankel H t ht)
      (1 : Matrix (Fin (2 + 1)) (Fin (2 + 1)) ℝ)
      hUnitDet
  simpa only [one_mul, Matrix.rank_one, Fintype.card_fin] using hRank

end GroundStatePosteriorJoint

namespace GroundStatePosteriorJoint

section ActualSmallFineKrylovRankThree

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n : ℕ)
local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "U" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector Hn 2
local notation "Fine" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    Hn 2 specialUnitaryTwoWilsonRankPositive
    (beta (n + 1)) (hbeta (n + 1))
local notation "Src" => p4Q2PE_actualThirdMomentCoefficient
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
local notation "S" => p4Q2HJ_actualRightPhysicalSourceSynthesis
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
local notation "M" => p4Q2HF_actualRightGIModalLinear
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
local notation "Mass" => p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
  Hn (beta n) (hbeta n)

/-- Unconditional original-Wilson finite-volume small-fine physical rank
three AND a strictly positive genuine two-posterior source mass AND an
actual signed GI receiver, using the SAME fixed interval and Schur source. -/
theorem p4Q2PZ37O_actualNonminimal_smallFine_Krylov_rankThree_postMass_trueGI
    (hH : 1 ≤ Hn) (hFrozen : 0 < beta n)
    (e e' : Link) (left₀ right₀ : Cfg) :
    ∃ delta : ℝ, 0 < delta ∧
      (0 < beta (n + 1) → beta (n + 1) < delta →
        LinearIndependent ℝ
          (fun j : Fin (2 + 1) => (Fine ^ (j : ℕ)) U) ∧
        0 < Mass (S 2 Src) (Finset.univ : Finset Link) ∧
        ∃ z : Cfg × Cfg, M 2 e z Src ≠ 0) := by
  obtain ⟨delta, hdelta, hAll⟩ :=
    p4Q2PZ37O_actualNonminimal_smallFine_hankel_postMass_trueGI
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hH hFrozen e e' left₀ right₀
  refine ⟨delta, hdelta, ?_⟩
  intro hFine hSmall
  obtain ⟨_hD2, _hD3, hDet, hMass, hGI⟩ := hAll hFine hSmall
  have hLi : LinearIndependent ℝ
      (fun j : Fin (2 + 1) => (Fine ^ (j : ℕ)) U) :=
    p4Q2PZ37O_originalPhysicalThreeKrylov_linearIndependent_of_det_pos
      Hn (beta (n + 1)) (hbeta (n + 1)) hDet
  exact ⟨hLi, hMass, hGI⟩

end ActualSmallFineKrylovRankThree
end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37O_originalPhysicalThreeKrylov_linearIndependent_of_det_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37O_originalPhysicalThreeHankel_rank_three_of_det_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37O_actualNonminimal_smallFine_Krylov_rankThree_postMass_trueGI
