import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianResolventNormBundle
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

open Set Filter Topology
open scoped InnerProductSpace NNReal

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The difference of two real spectral shifts is the scalar parameter difference. -/
theorem orthonormalDiagonalHamiltonianShiftedOperator_sub_shiftedOperator
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (lambda mu : ℝ) :
    orthonormalDiagonalHamiltonianShiftedOperator b a mu -
        orthonormalDiagonalHamiltonianShiftedOperator b a lambda =
      (lambda - mu) • (1 : E →L[ℝ] E) := by
  rw [orthonormalDiagonalHamiltonianShiftedOperator_eq_sub_smul_id,
    orthonormalDiagonalHamiltonianShiftedOperator_eq_sub_smul_id]
  module

/-- The two-parameter real resolvent identity below a common spectral gap. -/
theorem orthonormalDiagonalHamiltonianResolvent_sub_eq_smul_mul
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i)
    {lambda mu : ℝ} (hlambda : lambda < delta) (hmu : mu < delta) :
    orthonormalDiagonalHamiltonianResolvent b a lambda -
        orthonormalDiagonalHamiltonianResolvent b a mu =
      (lambda - mu) •
        (orthonormalDiagonalHamiltonianResolvent b a lambda *
          orthonormalDiagonalHamiltonianResolvent b a mu) := by
  have hRlambda :
      orthonormalDiagonalHamiltonianResolvent b a lambda *
          orthonormalDiagonalHamiltonianShiftedOperator b a lambda = 1 :=
    orthonormalDiagonalHamiltonianResolvent_mul_shiftedOperator
      b a delta lambda hdelta hlambda
  have hRmu :
      orthonormalDiagonalHamiltonianShiftedOperator b a mu *
          orthonormalDiagonalHamiltonianResolvent b a mu = 1 :=
    orthonormalDiagonalHamiltonianShiftedOperator_mul_resolvent
      b a delta mu hdelta hmu
  have hshift :
      orthonormalDiagonalHamiltonianShiftedOperator b a mu -
          orthonormalDiagonalHamiltonianShiftedOperator b a lambda =
        (lambda - mu) • (1 : E →L[ℝ] E) :=
    orthonormalDiagonalHamiltonianShiftedOperator_sub_shiftedOperator
      b a lambda mu
  calc
    orthonormalDiagonalHamiltonianResolvent b a lambda -
        orthonormalDiagonalHamiltonianResolvent b a mu =
      orthonormalDiagonalHamiltonianResolvent b a lambda * 1 -
        1 * orthonormalDiagonalHamiltonianResolvent b a mu := by
          rw [mul_one, one_mul]
    _ = orthonormalDiagonalHamiltonianResolvent b a lambda *
          (orthonormalDiagonalHamiltonianShiftedOperator b a mu *
            orthonormalDiagonalHamiltonianResolvent b a mu) -
        (orthonormalDiagonalHamiltonianResolvent b a lambda *
          orthonormalDiagonalHamiltonianShiftedOperator b a lambda) *
            orthonormalDiagonalHamiltonianResolvent b a mu := by
          rw [hRmu, hRlambda]
    _ = orthonormalDiagonalHamiltonianResolvent b a lambda *
          (orthonormalDiagonalHamiltonianShiftedOperator b a mu -
            orthonormalDiagonalHamiltonianShiftedOperator b a lambda) *
          orthonormalDiagonalHamiltonianResolvent b a mu := by
          noncomm_ring
    _ = orthonormalDiagonalHamiltonianResolvent b a lambda *
          ((lambda - mu) • (1 : E →L[ℝ] E)) *
          orthonormalDiagonalHamiltonianResolvent b a mu := by
          rw [hshift]
    _ = (lambda - mu) •
        (orthonormalDiagonalHamiltonianResolvent b a lambda *
          orthonormalDiagonalHamiltonianResolvent b a mu) := by
          simp [mul_smul_comm, smul_mul_assoc]

/-- Exact two-parameter operator-norm control from the resolvent identity. -/
theorem orthonormalDiagonalHamiltonianResolvent_sub_norm_le
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i)
    {lambda mu : ℝ} (hlambda : lambda < delta) (hmu : mu < delta) :
    ‖orthonormalDiagonalHamiltonianResolvent b a lambda -
        orthonormalDiagonalHamiltonianResolvent b a mu‖ ≤
      |lambda - mu| *
        ((delta - lambda)⁻¹ * (delta - mu)⁻¹) := by
  rw [orthonormalDiagonalHamiltonianResolvent_sub_eq_smul_mul
    b a delta hdelta hlambda hmu, norm_smul, Real.norm_eq_abs]
  have hlambdaNorm :=
    orthonormalDiagonalHamiltonianResolvent_norm_le_inv_sub
      b a delta lambda hdelta hlambda
  have hmuNorm :=
    orthonormalDiagonalHamiltonianResolvent_norm_le_inv_sub
      b a delta mu hdelta hmu
  have hproduct :
      ‖orthonormalDiagonalHamiltonianResolvent b a lambda‖ *
          ‖orthonormalDiagonalHamiltonianResolvent b a mu‖ ≤
        (delta - lambda)⁻¹ * (delta - mu)⁻¹ := by
    exact mul_le_mul hlambdaNorm hmuNorm
      (norm_nonneg _)
      (inv_nonneg.mpr (sub_nonneg.mpr hlambda.le))
  calc
    |lambda - mu| *
        ‖orthonormalDiagonalHamiltonianResolvent b a lambda *
          orthonormalDiagonalHamiltonianResolvent b a mu‖ ≤
      |lambda - mu| *
        (‖orthonormalDiagonalHamiltonianResolvent b a lambda‖ *
          ‖orthonormalDiagonalHamiltonianResolvent b a mu‖) :=
        mul_le_mul_of_nonneg_left (norm_mul_le _ _) (abs_nonneg _)
    _ ≤ |lambda - mu| *
        ((delta - lambda)⁻¹ * (delta - mu)⁻¹) :=
      mul_le_mul_of_nonneg_left hproduct (abs_nonneg _)

/-- Resolvent identity together with its exact quantitative parameter bound. -/
theorem orthonormalDiagonalHamiltonianResolventIdentity_package
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i)
    {lambda mu : ℝ} (hlambda : lambda < delta) (hmu : mu < delta) :
    orthonormalDiagonalHamiltonianResolvent b a lambda -
          orthonormalDiagonalHamiltonianResolvent b a mu =
        (lambda - mu) •
          (orthonormalDiagonalHamiltonianResolvent b a lambda *
            orthonormalDiagonalHamiltonianResolvent b a mu) ∧
      ‖orthonormalDiagonalHamiltonianResolvent b a lambda -
          orthonormalDiagonalHamiltonianResolvent b a mu‖ ≤
        |lambda - mu| *
          ((delta - lambda)⁻¹ * (delta - mu)⁻¹) :=
  ⟨orthonormalDiagonalHamiltonianResolvent_sub_eq_smul_mul
      b a delta hdelta hlambda hmu,
    orthonormalDiagonalHamiltonianResolvent_sub_norm_le
      b a delta hdelta hlambda hmu⟩

/-- The real resolvent bundled over the full open sub-gap parameter interval. -/
noncomputable def orthonormalDiagonalHamiltonianResolventFamily
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ) :
    Set.Iio delta → E →L[ℝ] E :=
  fun lambda => orthonormalDiagonalHamiltonianResolvent b a lambda

@[simp]
theorem orthonormalDiagonalHamiltonianResolventFamily_apply
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (lambda : Set.Iio delta) :
    orthonormalDiagonalHamiltonianResolventFamily b a delta lambda =
      orthonormalDiagonalHamiltonianResolvent b a lambda :=
  rfl

/-- Uniform Lipschitz control on parameter regions separated from the gap by `epsilon`. -/
theorem orthonormalDiagonalHamiltonianResolventFamily_lipschitzOn_subGapTruncation
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    LipschitzOnWith (Real.toNNReal (epsilon⁻¹ * epsilon⁻¹))
      (orthonormalDiagonalHamiltonianResolventFamily b a delta)
      {lambda : Set.Iio delta | (lambda : ℝ) ≤ delta - epsilon} := by
  apply LipschitzOnWith.of_dist_le'
  intro lambda hlambda mu hmu
  change (lambda : ℝ) ≤ delta - epsilon at hlambda
  change (mu : ℝ) ≤ delta - epsilon at hmu
  rw [dist_eq_norm]
  have hepsilonLambda : epsilon ≤ delta - (lambda : ℝ) := by
    linarith
  have hepsilonMu : epsilon ≤ delta - (mu : ℝ) := by
    linarith
  have hinvLambda :
      (delta - (lambda : ℝ))⁻¹ ≤ epsilon⁻¹ := by
    simpa only [one_div] using
      one_div_le_one_div_of_le hepsilon hepsilonLambda
  have hinvMu :
      (delta - (mu : ℝ))⁻¹ ≤ epsilon⁻¹ := by
    simpa only [one_div] using
      one_div_le_one_div_of_le hepsilon hepsilonMu
  have hmuInvNonneg : 0 ≤ (delta - (mu : ℝ))⁻¹ :=
    inv_nonneg.mpr (sub_nonneg.mpr mu.property.le)
  have hepsilonInvNonneg : 0 ≤ epsilon⁻¹ :=
    inv_nonneg.mpr hepsilon.le
  have hproduct :
      (delta - (lambda : ℝ))⁻¹ * (delta - (mu : ℝ))⁻¹ ≤
        epsilon⁻¹ * epsilon⁻¹ :=
    mul_le_mul hinvLambda hinvMu hmuInvNonneg hepsilonInvNonneg
  calc
    ‖orthonormalDiagonalHamiltonianResolventFamily b a delta lambda -
        orthonormalDiagonalHamiltonianResolventFamily b a delta mu‖ ≤
      |(lambda : ℝ) - (mu : ℝ)| *
        ((delta - (lambda : ℝ))⁻¹ * (delta - (mu : ℝ))⁻¹) := by
          simpa only [orthonormalDiagonalHamiltonianResolventFamily_apply] using
            (orthonormalDiagonalHamiltonianResolvent_sub_norm_le
              b a delta hdelta lambda.property mu.property)
    _ ≤ |(lambda : ℝ) - (mu : ℝ)| *
        (epsilon⁻¹ * epsilon⁻¹) :=
      mul_le_mul_of_nonneg_left hproduct (abs_nonneg _)
    _ = (epsilon⁻¹ * epsilon⁻¹) * dist lambda mu := by
      change |(lambda : ℝ) - (mu : ℝ)| *
          (epsilon⁻¹ * epsilon⁻¹) =
        (epsilon⁻¹ * epsilon⁻¹) * |(lambda : ℝ) - (mu : ℝ)|
      ring

/-- The sub-gap real resolvent family is locally Lipschitz in operator norm. -/
theorem orthonormalDiagonalHamiltonianResolventFamily_locallyLipschitz
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i) :
    LocallyLipschitz
      (orthonormalDiagonalHamiltonianResolventFamily b a delta) := by
  intro lambda
  let epsilon : ℝ := (delta - (lambda : ℝ)) / 2
  have hlambdaDelta : (lambda : ℝ) < delta := lambda.property
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    linarith
  refine ⟨Real.toNNReal (epsilon⁻¹ * epsilon⁻¹),
    {mu : Set.Iio delta | (mu : ℝ) ≤ delta - epsilon}, ?_, ?_⟩
  · refine mem_of_superset (Metric.ball_mem_nhds lambda hepsilon) ?_
    intro mu hmu
    change (mu : ℝ) ≤ delta - epsilon
    have hdist : |(mu : ℝ) - (lambda : ℝ)| < epsilon := by
      simpa [Real.dist_eq] using hmu
    have hlinear : (mu : ℝ) - (lambda : ℝ) < epsilon :=
      (le_abs_self _).trans_lt hdist
    dsimp [epsilon] at hlinear ⊢
    linarith
  · exact
      orthonormalDiagonalHamiltonianResolventFamily_lipschitzOn_subGapTruncation
        b a delta hdelta hepsilon

/-- The sub-gap real resolvent depends continuously on the spectral parameter. -/
theorem orthonormalDiagonalHamiltonianResolventFamily_continuous
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i) :
    Continuous (orthonormalDiagonalHamiltonianResolventFamily b a delta) :=
  (orthonormalDiagonalHamiltonianResolventFamily_locallyLipschitz
    b a delta hdelta).continuous

end

end MathlibAnalytic
end MGAP4D
