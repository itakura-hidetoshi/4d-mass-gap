import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBoundedColorCoercivity
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferFactorization
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Set
open scoped BigOperators InnerProductSpace InnerProduct

noncomputable section

set_option maxHeartbeats 1000000

/-- A self-adjoint idempotent has the metric-projection property against every
vector already fixed by it.

This is the Hilbert-space core of the conditional-expectation comparison.  It
uses only the two operator laws enjoyed by `condExpL2`: idempotence and
self-adjointness. -/
theorem realHilbert_idempotent_symmetric_residual_sq_le_of_fixed
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (P : E →L[ℝ] E)
    (hPid : P.comp P = P)
    (hPsymm : (P : E →ₗ[ℝ] E).IsSymmetric)
    (x z : E)
    (hz : P z = z) :
    ‖x - P x‖ ^ 2 ≤ ‖x - z‖ ^ 2 := by
  have hPpx : P (P x) = P x := by
    have h := congrArg (fun Q : E →L[ℝ] E => Q x) hPid
    simpa using h
  have hfixedDiff : P (P x - z) = P x - z := by
    rw [map_sub, hPpx, hz]
  have horth : inner ℝ (x - P x) (P x - z) = 0 := by
    rw [inner_sub_left]
    have hs :
        inner ℝ (P x) (P x - z) =
          inner ℝ x (P (P x - z)) :=
      hPsymm x (P x - z)
    rw [hs, hfixedDiff, sub_self]
  have hdecomp : x - z = (x - P x) + (P x - z) := by
    abel
  rw [hdecomp, norm_add_sq_real, horth]
  nlinarith [sq_nonneg ‖P x - z‖]

/-- Pythagoras for a self-adjoint idempotent, written in the squared-defect
form naturally produced by a conditional expectation. -/
theorem realHilbert_idempotent_symmetric_residual_sq_eq_defect
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (Q : E →L[ℝ] E)
    (hQid : Q.comp Q = Q)
    (hQsymm : (Q : E →ₗ[ℝ] E).IsSymmetric)
    (x : E) :
    ‖x - Q x‖ ^ 2 = ‖x‖ ^ 2 - ‖Q x‖ ^ 2 := by
  have hQQ : Q (Q x) = Q x := by
    have h := congrArg (fun R : E →L[ℝ] E => R x) hQid
    simpa using h
  have hs : inner ℝ (Q x) (Q x) = inner ℝ x (Q (Q x)) :=
    hQsymm x (Q x)
  rw [hQQ] at hs
  have hinner : inner ℝ x (Q x) = ‖Q x‖ ^ 2 := by
    calc
      inner ℝ x (Q x) = inner ℝ (Q x) (Q x) := hs.symm
      _ = ‖Q x‖ ^ 2 := real_inner_self_eq_norm_sq _
  rw [norm_sub_sq_real, hinner]
  ring

/-- Averaging finitely many conditional-expectation residuals cannot exceed
one coarser conditional-expectation residual when the coarse image is fixed by
every member of the family.

The normalization by `card C` is exact, so no volume factor is introduced. -/
theorem boundedColorNormalizedResidualEnergy_le_coarseProjectionResidual_sq
    {E C : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [Fintype C]
    [Nonempty C]
    (P : C → E →L[ℝ] E)
    (hPid : ∀ c, (P c).comp (P c) = P c)
    (hPsymm : ∀ c, ((P c : E →L[ℝ] E) : E →ₗ[ℝ] E).IsSymmetric)
    (Q : E →L[ℝ] E)
    (x : E)
    (hQfixed : ∀ c, P c (Q x) = Q x) :
    boundedColorNormalizedResidualEnergy P x ≤ ‖x - Q x‖ ^ 2 := by
  have hterm : ∀ c : C, ‖x - P c x‖ ^ 2 ≤ ‖x - Q x‖ ^ 2 := by
    intro c
    exact realHilbert_idempotent_symmetric_residual_sq_le_of_fixed
      (P c) (hPid c) (hPsymm c) x (Q x) (hQfixed c)
  have hsum :
      (∑ c : C, ‖x - P c x‖ ^ 2) ≤
        (Fintype.card C : ℝ) * ‖x - Q x‖ ^ 2 := by
    calc
      (∑ c : C, ‖x - P c x‖ ^ 2) ≤
          ∑ _c : C, ‖x - Q x‖ ^ 2 :=
        Finset.sum_le_sum fun c _hc => hterm c
      _ = (Fintype.card C : ℝ) * ‖x - Q x‖ ^ 2 := by simp
  have hcard : 0 < (Fintype.card C : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  unfold boundedColorNormalizedResidualEnergy
  calc
    (Fintype.card C : ℝ)⁻¹ * (∑ c : C, ‖x - P c x‖ ^ 2) ≤
        (Fintype.card C : ℝ)⁻¹ *
          ((Fintype.card C : ℝ) * ‖x - Q x‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = ‖x - Q x‖ ^ 2 := by
      rw [← mul_assoc, inv_mul_cancel₀ hcard.ne', one_mul]

/-- Exact data needed to compare a physical bounded-color residual with a
Wilson marginal conditional expectation.

`lift` is the Wilson marginal realization of the physical vector.  Its norm is
scaled by the one-slab feature-analysis norm.  `marginalCondExp` is the coarse
Wilson conditional expectation, and each `marginalColor c` is the corresponding
color conditional expectation.  The `coarse_fixed_by_color` field is precisely
the sigma-algebra nesting statement. -/
structure WilsonMarginalCondExpComparisonData
    {G H C : Type*}
    [NormedAddCommGroup G]
    [InnerProductSpace ℝ G]
    [NormedAddCommGroup H]
    [InnerProductSpace ℝ H]
    [CompleteSpace G]
    [CompleteSpace H]
    [Fintype C]
    (P : C → G →L[ℝ] G)
    (A : G →L[ℝ] H) where
  Marginal : Type*
  [marginalNormedAddCommGroup : NormedAddCommGroup Marginal]
  [marginalInnerProductSpace : InnerProductSpace ℝ Marginal]
  lift : G →L[ℝ] Marginal
  marginalColor : C → Marginal →L[ℝ] Marginal
  marginalCondExp : Marginal →L[ℝ] Marginal
  color_idempotent : ∀ c, (marginalColor c).comp (marginalColor c) = marginalColor c
  color_symmetric : ∀ c,
    ((marginalColor c : Marginal →L[ℝ] Marginal) : Marginal →ₗ[ℝ] Marginal).IsSymmetric
  coarse_idempotent : marginalCondExp.comp marginalCondExp = marginalCondExp
  coarse_symmetric :
    (marginalCondExp : Marginal →ₗ[ℝ] Marginal).IsSymmetric
  lift_color_intertwining : ∀ c x, lift (P c x) = marginalColor c (lift x)
  coarse_fixed_by_color : ∀ c x,
    marginalColor c (marginalCondExp (lift x)) = marginalCondExp (lift x)
  lift_norm_sq : ∀ x, ‖lift x‖ ^ 2 = ‖A‖ ^ 2 * ‖x‖ ^ 2
  coarse_norm_sq : ∀ x,
    ‖marginalCondExp (lift x)‖ ^ 2 = ‖A x‖ ^ 2

attribute [instance]
  WilsonMarginalCondExpComparisonData.marginalNormedAddCommGroup
  WilsonMarginalCondExpComparisonData.marginalInnerProductSpace

/-- The exact Wilson-marginal conditional-expectation comparison before the
final `A† A` step:

`‖A‖² E_color(x) ≤ ‖A‖² ‖x‖² - ‖A x‖²`.

This is the formal version of the law-of-total-variance step. -/
theorem WilsonMarginalCondExpComparisonData.analysisNormSq_mul_residual_le_analysisDefect
    {G H C : Type*}
    [NormedAddCommGroup G]
    [InnerProductSpace ℝ G]
    [NormedAddCommGroup H]
    [InnerProductSpace ℝ H]
    [CompleteSpace G]
    [CompleteSpace H]
    [Fintype C]
    [Nonempty C]
    (P : C → G →L[ℝ] G)
    (A : G →L[ℝ] H)
    (D : WilsonMarginalCondExpComparisonData P A)
    (x : G) :
    ‖A‖ ^ 2 * boundedColorNormalizedResidualEnergy P x ≤
      ‖A‖ ^ 2 * ‖x‖ ^ 2 - ‖A x‖ ^ 2 := by
  let y := D.lift x
  have hMarginal :
      boundedColorNormalizedResidualEnergy D.marginalColor y ≤
        ‖y - D.marginalCondExp y‖ ^ 2 :=
    boundedColorNormalizedResidualEnergy_le_coarseProjectionResidual_sq
      D.marginalColor D.color_idempotent D.color_symmetric
      D.marginalCondExp y
      (fun c => D.coarse_fixed_by_color c x)
  have hResidualScale :
      boundedColorNormalizedResidualEnergy D.marginalColor y =
        ‖A‖ ^ 2 * boundedColorNormalizedResidualEnergy P x := by
    unfold boundedColorNormalizedResidualEnergy
    have hterm : ∀ c : C,
        ‖y - D.marginalColor c y‖ ^ 2 =
          ‖A‖ ^ 2 * ‖x - P c x‖ ^ 2 := by
      intro c
      have hliftSub : D.lift (x - P c x) = y - D.marginalColor c y := by
        dsimp [y]
        rw [map_sub, D.lift_color_intertwining]
      rw [← hliftSub, D.lift_norm_sq]
    calc
      (Fintype.card C : ℝ)⁻¹ *
          (∑ c : C, ‖y - D.marginalColor c y‖ ^ 2) =
        (Fintype.card C : ℝ)⁻¹ *
          (∑ c : C, ‖A‖ ^ 2 * ‖x - P c x‖ ^ 2) := by
            apply congrArg
              (fun s : ℝ => ((Fintype.card C : ℝ)⁻¹) * s)
            apply Finset.sum_congr rfl
            intro c _hc
            exact hterm c
      _ = ‖A‖ ^ 2 *
          ((Fintype.card C : ℝ)⁻¹ *
            ∑ c : C, ‖x - P c x‖ ^ 2) := by
        rw [← Finset.mul_sum]
        ring
  have hCoarsePythagoras :
      ‖y - D.marginalCondExp y‖ ^ 2 =
        ‖A‖ ^ 2 * ‖x‖ ^ 2 - ‖A x‖ ^ 2 := by
    calc
      ‖y - D.marginalCondExp y‖ ^ 2 =
          ‖y‖ ^ 2 - ‖D.marginalCondExp y‖ ^ 2 :=
        realHilbert_idempotent_symmetric_residual_sq_eq_defect
          D.marginalCondExp D.coarse_idempotent D.coarse_symmetric y
      _ = ‖A‖ ^ 2 * ‖x‖ ^ 2 - ‖A x‖ ^ 2 := by
        rw [D.lift_norm_sq, D.coarse_norm_sq]
  rw [hResidualScale] at hMarginal
  rw [hCoarsePythagoras] at hMarginal
  exact hMarginal

/-- The second half of the comparison is purely operator-theoretic.  For
`T = A† A`, the analysis defect controls the raw squared norm defect of `T`. -/
theorem realHilbert_adjoint_comp_self_analysisDefect_le_rawSquaredDefect
    {G H : Type*}
    [NormedAddCommGroup G]
    [InnerProductSpace ℝ G]
    [NormedAddCommGroup H]
    [InnerProductSpace ℝ H]
    [CompleteSpace G]
    [CompleteSpace H]
    (A : G →L[ℝ] H)
    (x : G) :
    ‖A‖ ^ 2 * (‖A‖ ^ 2 * ‖x‖ ^ 2 - ‖A x‖ ^ 2) ≤
      ‖A‖ ^ 4 * ‖x‖ ^ 2 - ‖(A†).comp A x‖ ^ 2 := by
  have hAdjointNorm : ‖A†‖ = ‖A‖ := by
    exact ContinuousLinearMap.adjoint.norm_map A
  have hAx := ContinuousLinearMap.le_opNorm (A†) (A x)
  rw [hAdjointNorm] at hAx
  have hsq :
      ‖(A†) (A x)‖ * ‖(A†) (A x)‖ ≤
        (‖A‖ * ‖A x‖) * (‖A‖ * ‖A x‖) :=
    mul_self_le_mul_self (norm_nonneg _) hAx
  change
    ‖A‖ ^ 2 * (‖A‖ ^ 2 * ‖x‖ ^ 2 - ‖A x‖ ^ 2) ≤
      ‖A‖ ^ 4 * ‖x‖ ^ 2 - ‖(A†) (A x)‖ ^ 2
  simp only [pow_two] at hsq ⊢
  nlinarith

section PhysicalOneSlabWilsonMarginal

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "G" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N
local notation "T" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator H N hN beta hbeta
local notation "A" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
    H N hN beta hbeta
local notation "K" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
    H N hN beta hbeta

local instance periodicHypercubicEvenSpecialUnitaryPhysicalWilsonMarginal_completeSpace :
    CompleteSpace G :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H N).completeSpace_coe

/-- A Wilson marginal / conditional-expectation realization discharges the raw
model-side comparison obligation for the physical one-slab transfer.

The coefficient `eta ≤ 1` allows later geometric losses without changing the
exact marginal theorem.  With `eta = 1` the estimate is lossless:

`E_color(x) * ‖T‖² ≤ ‖T‖² ‖x‖² - ‖T x‖²`.
-/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlab_hcompare_of_wilsonMarginalCondExp
    {C : Type*}
    [Fintype C]
    [Nonempty C]
    (P : C → G →L[ℝ] G)
    (D : WilsonMarginalCondExpComparisonData P A)
    (eta : ℝ)
    (heta0 : 0 ≤ eta)
    (heta1 : eta ≤ 1)
    (x : K) :
    eta * boundedColorNormalizedResidualEnergy P (x : G) * ‖T‖ ^ 2 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRawTopOrthogonalSquaredDefect
        H N hN beta hbeta x := by
  have hMarginal := D.analysisNormSq_mul_residual_le_analysisDefect P A (x : G)
  have hAdjoint :=
    realHilbert_adjoint_comp_self_analysisDefect_le_rawSquaredDefect A (x : G)
  have hA0 : 0 ≤ ‖A‖ ^ 2 := sq_nonneg ‖A‖
  have hScaled := mul_le_mul_of_nonneg_left hMarginal hA0
  have hCombined :
      ‖A‖ ^ 4 * boundedColorNormalizedResidualEnergy P (x : G) ≤
        ‖A‖ ^ 4 * ‖(x : G)‖ ^ 2 - ‖T (x : G)‖ ^ 2 := by
    calc
      ‖A‖ ^ 4 * boundedColorNormalizedResidualEnergy P (x : G) =
          ‖A‖ ^ 2 *
            (‖A‖ ^ 2 * boundedColorNormalizedResidualEnergy P (x : G)) := by ring
      _ ≤ ‖A‖ ^ 2 * (‖A‖ ^ 2 * ‖(x : G)‖ ^ 2 - ‖A (x : G)‖ ^ 2) := hScaled
      _ ≤ ‖A‖ ^ 4 * ‖(x : G)‖ ^ 2 - ‖(A†).comp A (x : G)‖ ^ 2 := hAdjoint
      _ = ‖A‖ ^ 4 * ‖(x : G)‖ ^ 2 - ‖T (x : G)‖ ^ 2 := by
        rw [← periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_eq_adjoint_comp_analysis
          H N hN beta hbeta]
  have hResidualNonneg :
      0 ≤ boundedColorNormalizedResidualEnergy P (x : G) :=
    boundedColorNormalizedResidualEnergy_nonneg P (x : G)
  have hEtaScale :
      eta * (‖A‖ ^ 4 * boundedColorNormalizedResidualEnergy P (x : G)) ≤
        ‖A‖ ^ 4 * boundedColorNormalizedResidualEnergy P (x : G) := by
    have hbase : 0 ≤ ‖A‖ ^ 4 * boundedColorNormalizedResidualEnergy P (x : G) :=
      mul_nonneg (by positivity) hResidualNonneg
    nlinarith
  have hFinal := hEtaScale.trans hCombined
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRawTopOrthogonalSquaredDefect
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_eq_analysis_sq
    H N hN beta hbeta]
  convert hFinal using 1 <;> ring

end PhysicalOneSlabWilsonMarginal

end

end MathlibAnalytic
end MGAP4D
