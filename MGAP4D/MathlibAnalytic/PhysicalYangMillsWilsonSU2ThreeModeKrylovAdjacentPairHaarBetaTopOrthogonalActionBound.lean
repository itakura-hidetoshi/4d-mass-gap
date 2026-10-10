import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarActionBudgetPerturbativeDirichlet
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopSpectralProjection
import Mathlib.Tactic

/-!
# P4-Q2-AO: actual beta-dependent Wilson top-orthogonal action gap

The actual finite SU(N) gauge-invariant physical raw Wilson operator R_beta
satisfies ‖R_beta - Q_Haar‖ ≤ C_H beta, where Q_Haar=R_0 is exactly the
Haar-constant rank-one orthogonal projection. Rather than confusing the
beta-zero Haar-centered sector with the beta-dependent entire top-eigenspace,
we control the genuine beta-top orthogonal sector by using the chosen top
eigenvector u_beta and its quantitative Haar overlap:

    1 - 2 delta ≤ |⟪e_Haar, u_beta⟫|,  delta := C_H beta.

When 4 delta ≤ 1, every x orthogonal to the genuine u_beta satisfies

    ‖R_beta x‖ ≤ 3 delta ‖x‖.

The normalized transfer S_beta := R_beta / ‖R_beta‖ then obeys the
NONTRIVIAL beta-dependent entire-top-complement norm bound

    ‖S_beta|_(top eigenspace)⊥‖ ≤ 4 C_H beta.

This explicit weak-coupling gap is derived from the literal Wilson action
budget and the exact beta-zero Haar kernel, with NO proxy Gram, posterior
receiver, Dobrushin, new axioms, or uniform-volume extrapolation.
The weak-coupling window scales inversely with the finite slab size.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped InnerProductSpace InnerProduct

noncomputable section
set_option maxHeartbeats 2600000
set_option synthInstance.maxHeartbeats 850000

/-- Rank-one endpoint perturbation forces the genuine unit norm eigenvector
of the perturbed operator to overlap the original reference vector. -/
theorem p4Q2AO_realHilbert_rankOne_topEigenvector_overlap_lower
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (R : E →L[ℝ] E) (e u : E)
    (he : ‖e‖ = 1) (hu : ‖u‖ = 1)
    (huEig : R u = ‖R‖ • u)
    (delta : ℝ)
    (hPert : ‖R - InnerProductSpace.rankOne ℝ e e‖ ≤ delta) :
    1 - 2 * delta ≤ |inner ℝ e u| := by
  let Q : E →L[ℝ] E := InnerProductSpace.rankOne ℝ e e
  have hQnorm : ‖Q‖ = 1 := by
    dsimp [Q]
    rw [InnerProductSpace.norm_rankOne, he]
    norm_num
  have hNormDiff : |‖R‖ - ‖Q‖| ≤ delta :=
    (abs_norm_sub_norm_le R Q).trans hPert
  have hRLower : 1 - delta ≤ ‖R‖ := by
    rw [hQnorm] at hNormDiff
    have hLo := (abs_le.mp hNormDiff).1
    linarith
  have hRu : ‖R u‖ = ‖R‖ := by
    rw [huEig, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg R), hu,
      mul_one]
  have hQu : ‖Q u‖ = |inner ℝ e u| := by
    change ‖(inner ℝ e u) • e‖ = |inner ℝ e u|
    rw [norm_smul, Real.norm_eq_abs, he, mul_one]
  have hD : ‖(R - Q) u‖ ≤ delta := by
    calc
      ‖(R - Q) u‖ ≤ ‖R - Q‖ * ‖u‖ := (R - Q).le_opNorm u
      _ = ‖R - Q‖ := by rw [hu, mul_one]
      _ ≤ delta := hPert
  have hDec : R u = Q u + (R - Q) u := by
    simp only [ContinuousLinearMap.sub_apply]
    abel
  have hTri : ‖R u‖ ≤ ‖Q u‖ + ‖(R - Q) u‖ := by
    rw [hDec]
    exact norm_add_le _ _
  rw [hRu, hQu] at hTri
  linarith

/-- A small perturbation of a physical rank-one kernel suppresses the raw
transfer on the orthogonal complement of its ACTUAL perturbed top vector. -/
theorem p4Q2AO_realHilbert_rankOne_topOrthogonal_raw_apply_norm_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (R : E →L[ℝ] E) (e u : E)
    (he : ‖e‖ = 1) (hu : ‖u‖ = 1)
    (huEig : R u = ‖R‖ • u)
    (delta : ℝ)
    (hPert : ‖R - InnerProductSpace.rankOne ℝ e e‖ ≤ delta)
    (hSmall : 4 * delta ≤ 1)
    (x : E) (hx : inner ℝ u x = 0) :
    ‖R x‖ ≤ (3 * delta) * ‖x‖ := by
  let Q : E →L[ℝ] E := InnerProductSpace.rankOne ℝ e e
  have hOverlap : 1 - 2 * delta ≤ |inner ℝ e u| :=
    p4Q2AO_realHilbert_rankOne_topEigenvector_overlap_lower
      R e u he hu huEig delta hPert
  have hHalf : (1 / 2 : ℝ) ≤ |inner ℝ e u| := by
    linarith
  have hDu : ‖(R - Q) u‖ ≤ delta := by
    calc
      ‖(R - Q) u‖ ≤ ‖R - Q‖ * ‖u‖ := (R - Q).le_opNorm u
      _ = ‖R - Q‖ := by rw [hu, mul_one]
      _ ≤ delta := hPert
  have hInner :
      inner ℝ ((R - Q) u) x =
        - (inner ℝ e u) * (inner ℝ e x) := by
    change inner ℝ (R u - (inner ℝ e u) • e) x = _
    rw [huEig, inner_sub_left, real_inner_smul_left, real_inner_smul_left, hx]
    ring
  have hProduct :
      |inner ℝ e u| * |inner ℝ e x| ≤ delta * ‖x‖ := by
    calc
      |inner ℝ e u| * |inner ℝ e x| =
        |inner ℝ ((R - Q) u) x| := by rw [hInner, abs_mul, abs_neg]
      _ ≤ ‖(R - Q) u‖ * ‖x‖ := abs_real_inner_le_norm _ _
      _ ≤ delta * ‖x‖ :=
        mul_le_mul_of_nonneg_right hDu (norm_nonneg x)
  have hB : |inner ℝ e x| ≤ (2 * delta) * ‖x‖ := by
    have hMul :
        (1 / 2 : ℝ) * |inner ℝ e x| ≤
          |inner ℝ e u| * |inner ℝ e x| :=
      mul_le_mul_of_nonneg_right hHalf (abs_nonneg _)
    nlinarith [hMul, hProduct]
  have hQx : ‖Q x‖ = |inner ℝ e x| := by
    change ‖(inner ℝ e x) • e‖ = |inner ℝ e x|
    rw [norm_smul, Real.norm_eq_abs, he, mul_one]
  have hDx : ‖(R - Q) x‖ ≤ delta * ‖x‖ := by
    calc
      ‖(R - Q) x‖ ≤ ‖R - Q‖ * ‖x‖ := (R - Q).le_opNorm x
      _ ≤ delta * ‖x‖ :=
        mul_le_mul_of_nonneg_right hPert (norm_nonneg x)
  have hDec : R x = Q x + (R - Q) x := by
    simp only [ContinuousLinearMap.sub_apply]
    abel
  calc
    ‖R x‖ ≤ ‖Q x‖ + ‖(R - Q) x‖ := by
      rw [hDec]
      exact norm_add_le _ _
    _ ≤ (2 * delta) * ‖x‖ + delta * ‖x‖ := by
      rw [hQx]
      exact add_le_add hB hDx
    _ = (3 * delta) * ‖x‖ := by ring

/-- Normalizing a near-rank-one raw transfer retains an explicit upper bound
on its true top-eigenvector orthogonal sector, with no spectral projection
continuity hypothesis. -/
theorem p4Q2AO_realHilbert_rankOne_topOrthogonal_normalized_apply_norm_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (R : E →L[ℝ] E) (e u : E)
    (he : ‖e‖ = 1) (hu : ‖u‖ = 1)
    (huEig : R u = ‖R‖ • u)
    (delta : ℝ)
    (hPert : ‖R - InnerProductSpace.rankOne ℝ e e‖ ≤ delta)
    (hSmall : 4 * delta ≤ 1)
    (x : E) (hx : inner ℝ u x = 0) :
    ‖(‖R‖⁻¹ • R) x‖ ≤ (4 * delta) * ‖x‖ := by
  let Q : E →L[ℝ] E := InnerProductSpace.rankOne ℝ e e
  have hQnorm : ‖Q‖ = 1 := by
    dsimp [Q]
    rw [InnerProductSpace.norm_rankOne, he]
    norm_num
  have hNormDiff : |‖R‖ - ‖Q‖| ≤ delta :=
    (abs_norm_sub_norm_le R Q).trans hPert
  have hRLower : 1 - delta ≤ ‖R‖ := by
    rw [hQnorm] at hNormDiff
    have hLo := (abs_le.mp hNormDiff).1
    linarith
  have hThreeQuarters : (3 / 4 : ℝ) ≤ ‖R‖ := by
    linarith
  have hRPos : 0 < ‖R‖ := by linarith
  have hRaw := p4Q2AO_realHilbert_rankOne_topOrthogonal_raw_apply_norm_le
    R e u he hu huEig delta hPert hSmall x hx
  have hScale : ‖R‖ * ‖(‖R‖⁻¹ • R) x‖ = ‖R x‖ := by
    change ‖R‖ * ‖‖R‖⁻¹ • R x‖ = ‖R x‖
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hRPos]
    rw [mul_inv_cancel_left₀ hRPos.ne']
  have hMul :
      (3 / 4 : ℝ) * ‖(‖R‖⁻¹ • R) x‖ ≤
        ‖R‖ * ‖(‖R‖⁻¹ • R) x‖ :=
    mul_le_mul_of_nonneg_right hThreeQuarters (norm_nonneg _)
  nlinarith [hScale, hRaw, hMul]

/-- A generic Hilbert-space operator norm bound on the full top-eigenspace
orthogonal restriction, avoiding concrete subtype instance elaboration. -/
theorem p4Q2AO_realHilbert_topOrthogonal_opNorm_le_of_pointwise
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : E →L[ℝ] E)
    (hSym : (S : E →ₗ[ℝ] E).IsSymmetric)
    (M : ℝ) (hM : 0 ≤ M)
    (hApply : ∀ x : (realHilbertTopEigenspace S)ᗮ,
      ‖S (x : E)‖ ≤ M * ‖(x : E)‖) :
    ‖realHilbertTopEigenspaceOrthogonalRestriction S hSym‖ ≤ M := by
  let T := realHilbertTopEigenspaceOrthogonalRestriction S hSym
  apply ContinuousLinearMap.opNorm_le_bound T hM
  intro x
  change ‖S (x : E)‖ ≤ M * ‖x‖
  exact hApply x

local instance p4AOGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4AOCompact (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4AOSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4AOMeasurable (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4AOBorel (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4AOLinks (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance p4AOComplete (H N : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H N).completeSpace_coe

/-- The ACTUAL Wilson raw transfer on the orthogonal complement of its chosen
beta-dependent Perron top eigenvector is controlled by the genuine plaquette/link
action budget, not by the beta-zero Haar orthogonality assumption. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalRawWilson_betaTopOrthogonal_apply_norm_le
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hSmall : 4 *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
      beta ≤ 1)
    (x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (hx : inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
        H N hN beta hbeta) x = 0) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta x‖ ≤
      (3 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        beta) * ‖x‖ := by
  let R := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let e := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
    H N hN beta hbeta
  let delta := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H * beta
  have hPert : ‖R - InnerProductSpace.rankOne ℝ e e‖ ≤ delta := by
    have h := periodicHypercubicEvenSpecialUnitaryPhysicalRawWilson_norm_sub_betaZero_le_actionBudget
      H N hN beta hbeta
    simpa only [R, e, delta,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_zero_eq_rankOne
        H N hN] using h
  have hSmall' : 4 * delta ≤ 1 := by
    dsimp [delta]
    nlinarith [hSmall]
  have hRaw := p4Q2AO_realHilbert_rankOne_topOrthogonal_raw_apply_norm_le
    R e u
    (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_norm H N)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_norm
      H N hN beta hbeta)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_eigen
      H N hN beta hbeta)
    delta hPert hSmall' x hx
  simpa [R, delta, mul_assoc] using hRaw

/-- Genuine full top-eigenspace complement: normalized physical Wilson transfer
has explicit operator norm at most 4*C_H*beta in the finite-H weak-coupling
window. This is a beta-dependent physical gap bound, not a continuum result. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopOrthogonal_norm_le_actionBudget
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hSmall : 4 *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
      beta ≤ 1) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta‖ ≤
        4 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
          beta := by
  let R := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let e := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
    H N hN beta hbeta
  let delta := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H * beta
  have hdelta : 0 ≤ delta := mul_nonneg
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget_nonneg H)
    hbeta
  have hPert : ‖R - InnerProductSpace.rankOne ℝ e e‖ ≤ delta := by
    have h := periodicHypercubicEvenSpecialUnitaryPhysicalRawWilson_norm_sub_betaZero_le_actionBudget
      H N hN beta hbeta
    simpa only [R, e, delta,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_zero_eq_rankOne
        H N hN] using h
  have hSmall' : 4 * delta ≤ 1 := by
    dsimp [delta]
    nlinarith [hSmall]
  have hBound : 0 ≤ 4 *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        beta := by
    have hFour : 0 ≤ (4 : ℝ) * delta :=
      mul_nonneg (by norm_num) hdelta
    simpa only [delta, mul_assoc] using hFour
  let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  have hSym : (S : _ →ₗ[ℝ] _).IsSymmetric :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
      H N hN beta hbeta
  change ‖realHilbertTopEigenspaceOrthogonalRestriction S hSym‖ ≤
    4 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H * beta
  refine p4Q2AO_realHilbert_topOrthogonal_opNorm_le_of_pointwise
    S hSym _ hBound ?_
  intro x
  have hxOrth : (x :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) ∈
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
        H N hN beta hbeta)ᗮ := by
    exact x.property
  rw [Submodule.mem_orthogonal] at hxOrth
  have huOrth : inner ℝ u
      (x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) =
      0 :=
    hxOrth u (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_mem_topEigenspace
      H N hN beta hbeta)
  have hResult := p4Q2AO_realHilbert_rankOne_topOrthogonal_normalized_apply_norm_le
    R e u
    (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_norm H N)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_norm
      H N hN beta hbeta)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_eigen
      H N hN beta hbeta)
    delta hPert hSmall'
    (x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    huOrth
  change ‖(‖R‖⁻¹ • R)
    (x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)‖ ≤
    (4 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
      beta) * ‖x‖
  simpa only [delta, mul_assoc] using hResult

/-- The actual finite-volume normalized physical transfer gap is bounded from
below by 1 - 4*C_H*beta in the same beta-dependent regime. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap_ge_actionBudget
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hSmall : 4 *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        beta ≤ 1) :
    1 - 4 *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        beta ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
        H N hN beta hbeta := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
  have h :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopOrthogonal_norm_le_actionBudget
      H N hN beta hbeta hSmall
  linarith

end
end MathlibAnalytic
end MGAP4D
