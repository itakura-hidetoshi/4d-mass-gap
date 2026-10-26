import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalThirdMomentNonzeroBridgeV5_PZ37O
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGramPhysicalRank
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

/-!
# PZ37O — the original normalized Wilson physical Krylov span has rank three

Nonvanishing of the PZ37N original one- and two-slab Haar minor yields, via the
PZ37O/PE authentic two-moment pivot, a positive actual Hankel determinant.
The exact PZ4-Q2-PB physical Gram = Hankel theorem and AF's Gram rank =
physical synthesis image dimension then show that the three genuine
Gauss-law Hilbert vectors U, T U, T² U span a three-dimensional space.

This is the *physical source* rank-three theorem, not an unproved claim
of a volume-uniform detector singular value or a continuum mass gap.
-/

namespace MGAP4D.MathlibAnalytic
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000

namespace GroundStatePosteriorJoint

section OriginalKrylovRankThree

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "Phys" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule Hn 2
local notation "U" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector Hn 2
local notation "Fine" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    Hn 2 specialUnitaryTwoWilsonRankPositive
    (beta (n + 1)) (hbeta (n + 1))
local notation "Krylov" =>
  (fun j : Fin (2 + 1) => ((Fine ^ (j : ℕ)) U : Phys))

/-- The actual original physical three-by-three moment Hankel matrix,
not merely a Taylor polynomial, has rank precisely three for sufficiently
small positive fine coupling. -/
theorem p4Q2PZ37O_actualSmallFine_originalThreeHankel_rank_three
    (hH : 1 ≤ Hn) (hFrozen : 0 < beta n)
    (e e' : Link) (left₀ right₀ : Cfg) :
    ∃ delta : ℝ, 0 < delta ∧
      (0 < beta (n + 1) → beta (n + 1) < delta →
        (p4Q2PD_originalWilsonThreeHankel
          Hn (beta (n + 1)) (hbeta (n + 1))).rank = 3) := by
  obtain ⟨delta, hdelta, hDet⟩ :=
    p4Q2PZ37O_actualSmallFine_originalThreeHankel_det_pos
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hH hFrozen e e' left₀ right₀
  refine ⟨delta, hdelta, ?_⟩
  intro ht hsmall
  have hNonzero :
      (p4Q2PD_originalWilsonThreeHankel
        Hn (beta (n + 1)) (hbeta (n + 1))).det ≠ 0 :=
    ne_of_gt (hDet ht hsmall)
  have hUnitDet :
      IsUnit (p4Q2PD_originalWilsonThreeHankel
        Hn (beta (n + 1)) (hbeta (n + 1))).det :=
    isUnit_iff_ne_zero.mpr hNonzero
  have hRank :=
    Matrix.rank_mul_eq_left_of_isUnit_det
      (p4Q2PD_originalWilsonThreeHankel
        Hn (beta (n + 1)) (hbeta (n + 1)))
      (1 : Matrix (Fin (2 + 1)) (Fin (2 + 1)) ℝ)
      hUnitDet
  simpa only [one_mul, Matrix.rank_one, Fintype.card_fin] using hRank

/-- The three genuine normalized original Wilson physical Krylov
vectors U, T U, T² U have an image of real Hilbert dimension three.
This is a statement about the actual Gauss-law physical carrier. -/
theorem p4Q2PZ37O_actualSmallFine_originalPhysicalKrylov_finrank_three
    (hH : 1 ≤ Hn) (hFrozen : 0 < beta n)
    (e e' : Link) (left₀ right₀ : Cfg) :
    ∃ delta : ℝ, 0 < delta ∧
      (0 < beta (n + 1) → beta (n + 1) < delta →
        Module.finrank ℝ (p4Q2AD_realFiniteSynthesis Krylov).range = 3) := by
  obtain ⟨delta, hdelta, hRank⟩ :=
    p4Q2PZ37O_actualSmallFine_originalThreeHankel_rank_three
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hH hFrozen e e' left₀ right₀
  have hGram :
      Matrix.gram ℝ Krylov =
        p4Q2PD_originalWilsonThreeHankel
          Hn (beta (n + 1)) (hbeta (n + 1)) := by
    simpa only [p4Q2PD_originalWilsonThreeHankel] using
      (p4Q2PB_originalWilsonPhysicalGram_eq_actualHankel
        Hn (beta (n + 1)) (hbeta (n + 1)) 2)
  refine ⟨delta, hdelta, ?_⟩
  intro ht hsmall
  calc
    Module.finrank ℝ (p4Q2AD_realFiniteSynthesis Krylov).range =
        (Matrix.gram ℝ Krylov).rank :=
          (p4Q2AF_realFiniteGram_rank_eq_physical_finrank Krylov).symm
    _ = (p4Q2PD_originalWilsonThreeHankel
          Hn (beta (n + 1)) (hbeta (n + 1))).rank := by
          rw [hGram]
    _ = 3 := hRank ht hsmall

end OriginalKrylovRankThree

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37O_actualSmallFine_originalThreeHankel_rank_three
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37O_actualSmallFine_originalPhysicalKrylov_finrank_three
