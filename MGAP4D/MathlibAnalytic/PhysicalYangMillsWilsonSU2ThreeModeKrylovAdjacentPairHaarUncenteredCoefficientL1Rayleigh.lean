import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarUnitReceiverDirichletExplicitBeta
import Mathlib.Tactic

/-!
# P4-Q2: original uncentered right-Krylov Gram without hidden physical coefficients

PR #5318 established a complete finite-volume ORIGINAL Wilson SU(2)
right-Krylov Rayleigh upper bound. Its constant receiver contribution
retains the scalar inner product
  inner(u_H, sum_j a_j R(n,j)).
Here we eliminate that remaining input-dependent physical inner product
with the genuine norm-one finite right-Krylov orbit. The exact original
fine one-slab normalized physical transfer has norm one, so every right
Krylov factor has Hilbert norm at most one. An abstract real Hilbert
Cauchy--Schwarz argument, coupled to the triangle inequality, gives
  inner(u_H, sum_j a_j R(n,j))^2 <= (sum_j |a_j|)^2.

The resulting ORIGINAL uncentered physical Gram estimate depends only
on the explicit two physical Wilson couplings beta(n), beta(n+1), the
finite spatial geometry H, depth r, and the real coefficient vector a:
  a*G_right a <=
   2 * ((sum_j |a_j|)^2 * EunitExplicit_H(beta(n))
       + |Links(H)| *
           (C_H(beta(n)) *
             sum_j |a_j| j M_H(beta(n+1)))^2).

EunitExplicit is the actual original positive-beta Wilson receiver
majorant from #5318; it is not an invented Haar posterior. No assertion
of uniformity in spatial volume, r, or continuum Yang--Mills mass gap.
No Dobrushin, surrogate measure, sorry/admit or new axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 750000

/-- A norm-one real Hilbert reference has bounded Fourier coefficient
against every finite combination of inputs from the norm unit ball.
No count of modes is inserted before the actual coefficients. -/
private theorem realHilbert_unit_inner_sum_smul_sq_le_l1_sq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι]
    (u : E) (hu : ‖u‖ = 1) (f : ι → E)
    (hf : ∀ i, ‖f i‖ ≤ 1) (a : ι → ℝ) :
    (inner ℝ u (∑ i : ι, a i • f i)) ^ 2 ≤
      (∑ i : ι, |a i|) ^ 2 := by
  classical
  let F := ∑ i : ι, a i • f i
  let L : ℝ := ∑ i : ι, |a i|
  have hNorm : ‖F‖ ≤ L := by
    change ‖∑ i : ι, a i • f i‖ ≤ ∑ i : ι, |a i|
    apply norm_sum_le_of_le
    intro i _hi
    calc
      ‖a i • f i‖ = |a i| * ‖f i‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      _ ≤ |a i| * 1 :=
        mul_le_mul_of_nonneg_left (hf i) (abs_nonneg _)
      _ = |a i| := mul_one _
  have hCS : |inner ℝ u F| ≤ ‖F‖ := by
    calc
      |inner ℝ u F| ≤ ‖u‖ * ‖F‖ :=
        abs_real_inner_le_norm u F
      _ = ‖F‖ := by rw [hu, one_mul]
  have hAbs : |inner ℝ u F| ≤ L := hCS.trans hNorm
  have hSq : |inner ℝ u F| ^ 2 ≤ L ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) hAbs 2
  simpa only [F, L, sq_abs] using hSq

local instance p4RightCoeffTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4RightCoeffCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4RightCoeffSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4RightCoeffMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4RightCoeffBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4RightCoeffLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Original fine physical right Krylov coefficients, still carrying
fine beta(n+1), are bounded purely by their real coefficient ℓ¹ norm. -/
theorem fineRightKrylov_constantCoefficient_sq_le_l1_sq
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ) :
    (inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector
          (halfExtent (n + 1)) 2)
        (∑ j : Fin (r + 1), a j •
          physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n (j : ℕ))) ^ 2 ≤
      (∑ j : Fin (r + 1), |a j|) ^ 2 := by
  classical
  let H := halfExtent (n + 1)
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let f : Fin (r + 1) →
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2 :=
    fun j => physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n (j : ℕ)
  have hu : ‖u‖ = 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_norm H 2
  have hf (j : Fin (r + 1)) : ‖f j‖ ≤ 1 :=
    physicalYangMillsSU2AdjacentFinePairOrbitRightFactor_norm_le_one
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n (j : ℕ)
  exact realHilbert_unit_inner_sum_smul_sq_le_l1_sq u hu f hf a

/-- The authentic positive-beta Wilson SU(2) constant-unit receiver
majorant is nonnegative for every finite spatial volume. -/
theorem physicalOriginalUnitReceiverExplicitBetaMajorant_SU2_nonneg
    (H : ℕ) (beta : ℝ) :
    0 ≤ physicalOriginalUnitReceiverExplicitBetaMajorant_SU2 H beta := by
  unfold physicalOriginalUnitReceiverExplicitBetaMajorant_SU2
  apply mul_nonneg (Nat.cast_nonneg _)
  exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    (add_nonneg (sq_nonneg _) (sq_nonneg _))

/-- TRUE uncentered right physical Krylov Gram, with the exact
posterior and both original Wilson beta couplings: its Rayleigh
upper bound now has NO hidden inner product with the physical orbit. -/
theorem fineRightKrylovPairHaarResidualGram_rayleigh_le_coefficientL1_explicitTwoBeta
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ) :
    star a ⬝ᵥ
      (Matrix.mulVec
        (fineRightKrylovPairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) a) ≤
      2 * (
        (∑ j : Fin (r + 1), |a j|) ^ 2 *
          physicalOriginalUnitReceiverExplicitBetaMajorant_SU2
            (halfExtent (n + 1)) (beta n) +
        (Fintype.card
            (PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1))) : ℝ) *
          (physicalOriginalOrthogonalReceiverBetaLipschitzBudget
              (halfExtent (n + 1)) (beta n) *
            (∑ j : Fin (r + 1), |a j| *
              ((j : ℝ) *
                physicalOriginalNormalizedTransferConstantStepBetaBudget
                  (halfExtent (n + 1)) (beta (n + 1))))) ^ 2) := by
  classical
  let H := halfExtent (n + 1)
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let F := ∑ j : Fin (r + 1), a j •
    physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n (j : ℕ)
  let c : ℝ := inner ℝ u F
  let L : ℝ := ∑ j : Fin (r + 1), |a j|
  let M : ℝ := physicalOriginalUnitReceiverExplicitBetaMajorant_SU2 H (beta n)
  let W : ℝ :=
    (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
      (physicalOriginalOrthogonalReceiverBetaLipschitzBudget H (beta n) *
        (∑ j : Fin (r + 1), |a j| *
          ((j : ℝ) *
            physicalOriginalNormalizedTransferConstantStepBetaBudget
              H (beta (n + 1))))) ^ 2
  have hPrev :
      star a ⬝ᵥ
        (Matrix.mulVec
          (fineRightKrylovPairHaarResidualGram
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r) a) ≤
      2 * (c ^ 2 * M + W) := by
    simpa only [c, M, W, H, F, u] using
      (fineRightKrylovPairHaarResidualGram_rayleigh_le_explicitOriginalTwoBeta
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r a)
  have hCoeff : c ^ 2 ≤ L ^ 2 := by
    simpa only [c, L, H, F, u] using
      (fineRightKrylov_constantCoefficient_sq_le_l1_sq
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r a)
  have hM : 0 ≤ M :=
    physicalOriginalUnitReceiverExplicitBetaMajorant_SU2_nonneg H (beta n)
  have hTerm : c ^ 2 * M ≤ L ^ 2 * M :=
    mul_le_mul_of_nonneg_right hCoeff hM
  have hTotal : 2 * (c ^ 2 * M + W) ≤ 2 * (L ^ 2 * M + W) :=
    mul_le_mul_of_nonneg_left
      (add_le_add_right hTerm W) (by norm_num)
  change
    star a ⬝ᵥ
      (Matrix.mulVec
        (fineRightKrylovPairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) a) ≤
      2 * (L ^ 2 * M + W)
  exact hPrev.trans hTotal

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
