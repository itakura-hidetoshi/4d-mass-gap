import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarFineRightExplicitTwoCouplingBeta
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPhysicalInputRayleigh
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Tactic

/-!
# P4-Q2: weighted Rayleigh control for the actual centered fine-right Krylov Gram

PR #5313 proved that the genuine centered fine-right physical Krylov factor
  g_(n,j) = R(n,j) - inner(u_H,R(n,j)) u_H
obeys
  ||g_(n,j)|| <= j * M_H(beta(n+1)),
where M is the EXPLICIT finite-H physical normalized transfer-step Wilson
budget, and independently the original frozen-beta posterior receiver obeys
  A_(beta(n),H)(g) <= |Links(H)| * (C_H(beta(n)) ||g||)^2
for each physical constant-orthogonal g.

This file forms the actual CENTERED family of the fine-right Krylov inputs
and the ORIGINAL pair-Haar receiver Gram for the frozen beta(n) posterior.
Its finite-mode real Gram matrix is positive semidefinite. For arbitrary
real coefficients a_j, the combined physical input is exactly constant-
orthogonal, even if the original uncentered Krylov factors are not.

The full Rayleigh form is bounded with coefficient ONE and a weighted
coefficient sum, not a fabricated uniform-in-r or uniform-in-volume constant:
  a^* G_centered a
    <= |Links(H)| *
       (C_H(beta(n)) * SUM_j |a_j| j M_H(beta(n+1)))^2.

This keeps beta(n) and beta(n+1) independent; preserves original normalized
physical transfer, the signed pair-Haar receiver and the original joint
conditional expectations. The centered Gram is NOT asserted equal to the
uncentered right Gram, whose constant-vacuum part still matters.
No Dobrushin, alternate posterior, volume-uniform bound or continuum gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance p4CenteredGramTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4CenteredGramCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4CenteredGramSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4CenteredGramMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4CenteredGramBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4CenteredGramLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- The ORIGINAL true frozen-beta pair-Haar posterior-residual Gram of the
actual fine-right physical Krylov family after exact projection away from
the canonical physical Haar constant.  This is an additional centered
compression, not a replacement for the existing uncentered Krylov Gram. -/
noncomputable def fineRightCenteredKrylovPairHaarResidualGram
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ :=
  pairHaarSpatialLinkResidualGram
    (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
    (beta n) (hbeta n)
    (fun j : Fin (r + 1) =>
      normalizedPhysicalOneSlabPairHaarReceiver
        (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
        (beta n) (hbeta n)
        (fineRightConstantOrthogonalKrylovInput
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n (j : ℕ)))

/-- The centered actual Krylov Gram is positive semidefinite because
every summand is the Gram of the true physical posterior residuals. -/
theorem fineRightCenteredKrylovPairHaarResidualGram_posSemidef
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) :
    (fineRightCenteredKrylovPairHaarResidualGram
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r).PosSemidef := by
  unfold fineRightCenteredKrylovPairHaarResidualGram
  exact pairHaarSpatialLinkResidualGram_posSemidef
    (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
    (beta n) (hbeta n) _

/-- Any finite real combination of genuinely centered fine-right
Krylov physical vectors remains exactly orthogonal to the physical
constant unit, without imposing orthogonality on the original factors. -/
theorem fineRightCenteredKrylovCombination_inner_constant_zero
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ) :
    inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector
        (halfExtent (n + 1)) 2)
      (∑ j : Fin (r + 1), a j •
        fineRightConstantOrthogonalKrylovInput
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n (j : ℕ)) = 0 := by
  classical
  let H := halfExtent (n + 1)
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let g : Fin (r + 1) →
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2 :=
    fun j => fineRightConstantOrthogonalKrylovInput
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n (j : ℕ)
  have hOrth (j : Fin (r + 1)) : inner ℝ u (g j) = 0 :=
    fineRightConstantOrthogonalKrylovInput_inner_zero
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n (j : ℕ)
  change inner ℝ u (∑ j : Fin (r + 1), a j • g j) = 0
  calc
    inner ℝ u (∑ j : Fin (r + 1), a j • g j) =
        ∑ j : Fin (r + 1), inner ℝ u (a j • g j) := by
          exact map_sum (innerₛₗ ℝ u) _ _
    _ = ∑ j : Fin (r + 1), a j * inner ℝ u (g j) := by
      apply Finset.sum_congr rfl
      intro j _hj
      exact real_inner_smul_right u (g j) (a j)
    _ = 0 := by simp [hOrth]

/-- True physical Hilbert norm of an arbitrary centered fine-right
combination, controlled by the depth-weighted coefficient ℓ¹ sum.
This is sharper in form than a mode-count times one-link worst case. -/
theorem fineRightCenteredKrylovCombination_norm_le_weightedFineBeta
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ) :
    ‖∑ j : Fin (r + 1), a j •
        fineRightConstantOrthogonalKrylovInput
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n (j : ℕ)‖ ≤
      ∑ j : Fin (r + 1), |a j| *
        ((j : ℝ) *
          physicalOriginalNormalizedTransferConstantStepBetaBudget
            (halfExtent (n + 1)) (beta (n + 1))) := by
  classical
  let H := halfExtent (n + 1)
  let M := physicalOriginalNormalizedTransferConstantStepBetaBudget H (beta (n + 1))
  let g : Fin (r + 1) →
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2 :=
    fun j => fineRightConstantOrthogonalKrylovInput
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n (j : ℕ)
  change ‖∑ j : Fin (r + 1), a j • g j‖ ≤
      ∑ j : Fin (r + 1), |a j| * ((j : ℝ) * M)
  apply norm_sum_le_of_le
  intro j _hj
  have hMode : ‖g j‖ ≤ (j : ℝ) * M := by
    simpa only [g, M, H] using
      (fineRightConstantOrthogonalKrylovInput_norm_le_explicitFineBeta
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n (j : ℕ))
  calc
    ‖a j • g j‖ = |a j| * ‖g j‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    _ ≤ |a j| * ((j : ℝ) * M) :=
      mul_le_mul_of_nonneg_left hMode (abs_nonneg _)

/-- Explicit original FROZEN posterior Gram Rayleigh bound for all
coefficients of the centered genuine FINE Krylov modes, with
independent fine/frozen beta factors, coefficient one, and the
true finite-volume Wilson-link count. -/
theorem fineRightCenteredKrylovPairHaarResidualGram_rayleigh_le_weightedTwoBeta
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ) :
    star a ⬝ᵥ (Matrix.mulVec
      (fineRightCenteredKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a) ≤
      (Fintype.card
        (PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1))) : ℝ) *
      (physicalOriginalOrthogonalReceiverBetaLipschitzBudget
        (halfExtent (n + 1)) (beta n) *
        (∑ j : Fin (r + 1), |a j| *
          ((j : ℝ) *
            physicalOriginalNormalizedTransferConstantStepBetaBudget
              (halfExtent (n + 1)) (beta (n + 1))))) ^ 2 := by
  classical
  let H := halfExtent (n + 1)
  let C := physicalOriginalOrthogonalReceiverBetaLipschitzBudget H (beta n)
  let M := physicalOriginalNormalizedTransferConstantStepBetaBudget H (beta (n + 1))
  let g : Fin (r + 1) →
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2 :=
    fun j => fineRightConstantOrthogonalKrylovInput
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n (j : ℕ)
  let W : ℝ := ∑ j : Fin (r + 1), |a j| * ((j : ℝ) * M)
  have hOrth : inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)
      (∑ j : Fin (r + 1), a j • g j) = 0 :=
    fineRightCenteredKrylovCombination_inner_constant_zero
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a
  have hRay : star a ⬝ᵥ
      (Matrix.mulVec
        (fineRightCenteredKrylovPairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) a) ≤
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
        (C * ‖∑ j : Fin (r + 1), a j • g j‖) ^ 2 := by
    simpa only [fineRightCenteredKrylovPairHaarResidualGram, g, C, H] using
      (pairHaarSpatialLinkResidualGram_orthogonal_rayleigh_le_explicitBetaSquared
        H 2 specialUnitaryTwoWilsonRankPositive
        (beta n) (hbeta n) g a hOrth)
  have hNorm : ‖∑ j : Fin (r + 1), a j • g j‖ ≤ W := by
    simpa only [g, W, M, H] using
      (fineRightCenteredKrylovCombination_norm_le_weightedFineBeta
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r a)
  have hC : 0 ≤ C :=
    physicalOriginalOrthogonalReceiverBetaLipschitzBudget_nonneg
      H (beta n) (hbeta n)
  have hScale : C * ‖∑ j : Fin (r + 1), a j • g j‖ ≤ C * W :=
    mul_le_mul_of_nonneg_left hNorm hC
  have hSquare :
      (C * ‖∑ j : Fin (r + 1), a j • g j‖) ^ 2 ≤ (C * W) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hC (norm_nonneg _)) hScale 2
  change star a ⬝ᵥ (Matrix.mulVec
      (fineRightCenteredKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a) ≤
    (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) * (C * W) ^ 2
  exact hRay.trans
    (mul_le_mul_of_nonneg_left hSquare (Nat.cast_nonneg _))

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
