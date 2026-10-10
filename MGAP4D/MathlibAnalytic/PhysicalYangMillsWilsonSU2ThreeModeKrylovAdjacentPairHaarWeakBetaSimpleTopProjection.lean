import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarBetaTopOrthogonalActionBound
import Mathlib.Tactic

/-!
# P4-Q2-AP: one-dimensional genuine Wilson top sector and Haar projection control

AO proves a quantitative bound on the ACTUAL beta-dependent entire-top
orthogonal physical transfer using the literal Wilson plaquette/link budget.

Here that strict bound eliminates a second independent eigenvalue-one state:
under 4*C_H*beta < 1, every physical top-fixed state is a real scalar
multiple of the chosen actual physical top eigenvector. The entire canonical
top eigenspace is therefore the genuine rank-one line and the canonical full
top spectral projection is exactly its unit rank-one operator.

Independently, the unnormalized ACTUAL Wilson kernel R_beta differs from
its beta=0 Haar rank-one endpoint by at most C_H*beta. Thus every physical
beta-top state x satisfies

    ‖x - R_0 x‖ ≤ 2*C_H*beta*‖x‖.

Since the canonical top projection fixes x, this is the on-top spectral
projection stability estimate

    ‖(P_beta - R_0) x‖ ≤ 2*C_H*beta*‖x‖  (x in range P_beta).

This is a genuine projection comparison on the entire actual top sector,
not an assertion of global operator-norm continuity or volume-uniform gap.
The plaquette/link count C_H explicitly depends on the finite volume.
No fictional posterior or proxy operator, no new axiom/sorry/admit.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped InnerProductSpace InnerProduct

noncomputable section
set_option maxHeartbeats 2600000
set_option synthInstance.maxHeartbeats 850000

/-- As in the canonical spectral projection definition, the closed top
eigenspace carries the required complete normed-submodule instance. -/
local instance p4APTopEigenspaceComplete
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (S : E →L[ℝ] E) :
    CompleteSpace (realHilbertTopEigenspace S) :=
  (realHilbertTopEigenspace_isClosed S).completeSpace_coe

/-- An actual fixed vector has no component orthogonal to a unit fixed
state if the operator is strictly contractive on that orthogonal hyperplane. -/
theorem p4Q2AP_realHilbert_fixed_eq_scalar_of_orthogonal_contraction
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : E →L[ℝ] E) (u : E)
    (hu : ‖u‖ = 1) (huFix : S u = u)
    (q : ℝ) (hq : q < 1)
    (hOrth : ∀ y : E, inner ℝ u y = 0 → ‖S y‖ ≤ q * ‖y‖)
    (x : E) (hx : S x = x) :
    ∃ c : ℝ, x = c • u := by
  let c : ℝ := inner ℝ u x
  let y : E := x - c • u
  have hyOrth : inner ℝ u y = 0 := by
    dsimp [y, c]
    rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hu]
    norm_num
  have hyFix : S y = y := by
    dsimp [y]
    rw [map_sub, map_smul, hx, huFix]
  have hyBound := hOrth y hyOrth
  rw [hyFix] at hyBound
  have hyZero : y = 0 := by
    by_contra hyNe
    have hyPos : 0 < ‖y‖ := norm_pos_iff.mpr hyNe
    have hProduct : 0 < (1 - q) * ‖y‖ :=
      mul_pos (sub_pos.mpr hq) hyPos
    nlinarith
  exact ⟨c, sub_eq_zero.mp hyZero⟩

/-- The FULL eigenvalue-one subspace equals the one-dimensional line through
the genuine unit fixed state, without assuming a chosen proxy vacuum sector. -/
theorem p4Q2AP_realHilbert_topEigenspace_eq_span
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : E →L[ℝ] E) (u : E)
    (hu : ‖u‖ = 1) (huFix : S u = u)
    (q : ℝ) (hq : q < 1)
    (hOrth : ∀ y : E, inner ℝ u y = 0 → ‖S y‖ ≤ q * ‖y‖) :
    realHilbertTopEigenspace S = ℝ ∙ u := by
  ext x
  rw [realHilbertTopEigenspace_mem S x]
  constructor
  · intro hx
    obtain ⟨c, hc⟩ :=
      p4Q2AP_realHilbert_fixed_eq_scalar_of_orthogonal_contraction
        S u hu huFix q hq hOrth x hx
    exact Submodule.mem_span_singleton.mpr ⟨c, hc.symm⟩
  · intro hx
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
    rw [← hc, map_smul, huFix]

/-- Orthogonal projection onto an abstract closed one-dimensional line.
Using the universal characterization rather than rewriting the submodule
avoids transporting a dependent HasOrthogonalProjection instance. -/
theorem p4Q2AP_realHilbert_starProjection_eq_rankOne_of_eq_span
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : Submodule ℝ E) [F.HasOrthogonalProjection]
    (u : E) (hu : ‖u‖ = 1) (hLine : F = ℝ ∙ u) :
    F.starProjection = InnerProductSpace.rankOne ℝ u u := by
  apply ContinuousLinearMap.ext
  intro x
  rw [InnerProductSpace.rankOne_apply]
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · have huF : u ∈ F := by
      rw [hLine]
      exact Submodule.mem_span_singleton_self u
    exact F.smul_mem (inner ℝ u x) huF
  · rw [hLine, Submodule.mem_orthogonal]
    intro z hz
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hz
    have hBase : inner ℝ u (x - inner ℝ u x • u) = 0 := by
      rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hu]
      norm_num
    calc
      inner ℝ z (x - inner ℝ u x • u) =
          inner ℝ (c • u) (x - inner ℝ u x • u) := by rw [hc]
      _ = c * inner ℝ u (x - inner ℝ u x • u) := by rw [real_inner_smul_left]
      _ = 0 := by rw [hBase, mul_zero]

/-- Consequently the canonical full-top projection is EXACTLY the rank-one
orthogonal projection onto the true beta-top unit eigenvector. -/
theorem p4Q2AP_realHilbert_topEigenspaceProjection_eq_rankOne
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (S : E →L[ℝ] E) (u : E)
    (hu : ‖u‖ = 1) (huFix : S u = u)
    (q : ℝ) (hq : q < 1)
    (hOrth : ∀ y : E, inner ℝ u y = 0 → ‖S y‖ ≤ q * ‖y‖) :
    realHilbertTopEigenspaceProjection S = InnerProductSpace.rankOne ℝ u u := by
  have hLine := p4Q2AP_realHilbert_topEigenspace_eq_span
    S u hu huFix q hq hOrth
  change (realHilbertTopEigenspace S).starProjection =
    InnerProductSpace.rankOne ℝ u u
  exact p4Q2AP_realHilbert_starProjection_eq_rankOne_of_eq_span
    (realHilbertTopEigenspace S) u hu hLine

/-- A genuine eigenstate at the raw top norm is O(delta)-close to the
beta-zero Haar rank-one projection, directly from the raw operator itself. -/
theorem p4Q2AP_realHilbert_rawTop_eigen_HaarProjection_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (R : E →L[ℝ] E) (e x : E)
    (he : ‖e‖ = 1)
    (hx : R x = ‖R‖ • x)
    (delta : ℝ)
    (hPert : ‖R - InnerProductSpace.rankOne ℝ e e‖ ≤ delta) :
    ‖x - InnerProductSpace.rankOne ℝ e e x‖ ≤
      (2 * delta) * ‖x‖ := by
  let Q : E →L[ℝ] E := InnerProductSpace.rankOne ℝ e e
  have hQnorm : ‖Q‖ = 1 := by
    dsimp [Q]
    rw [InnerProductSpace.norm_rankOne, he]
    norm_num
  have hNormDiff : |1 - ‖R‖| ≤ delta := by
    have h := (abs_norm_sub_norm_le R Q).trans hPert
    rw [hQnorm] at h
    simpa only [abs_sub_comm] using h
  have hScalar : ‖(1 - ‖R‖) • x‖ ≤ delta * ‖x‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hNormDiff (norm_nonneg x)
  have hPertX : ‖(R - Q) x‖ ≤ delta * ‖x‖ := by
    calc
      ‖(R - Q) x‖ ≤ ‖R - Q‖ * ‖x‖ := (R - Q).le_opNorm x
      _ ≤ delta * ‖x‖ :=
        mul_le_mul_of_nonneg_right hPert (norm_nonneg x)
  have hDecompose :
      x - Q x = (1 - ‖R‖) • x + (R - Q) x := by
    rw [ContinuousLinearMap.sub_apply, hx]
    module
  change ‖x - Q x‖ ≤ (2 * delta) * ‖x‖
  calc
    ‖x - Q x‖ = ‖(1 - ‖R‖) • x + (R - Q) x‖ := by rw [hDecompose]
    _ ≤ ‖(1 - ‖R‖) • x‖ + ‖(R - Q) x‖ := norm_add_le _ _
    _ ≤ delta * ‖x‖ + delta * ‖x‖ := add_le_add hScalar hPertX
    _ = (2 * delta) * ‖x‖ := by ring

local instance p4APGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4APCompact (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4APSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4APMeasurable (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4APBorel (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4APLinks (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance p4APComplete (H N : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H N).completeSpace_coe

/-- Actual normalized physical Wilson transfer is controlled on vectors
orthogonal to its ACTUAL beta-dependent chosen top eigenvector. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalNormalizedWilson_topVectorOrthogonal_norm_le_actionBudget
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hSmall : 4 *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
      beta ≤ 1)
    (x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (hx : inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
        H N hN beta hbeta) x = 0) :
    ‖periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta x‖ ≤
      (4 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
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
  have h := p4Q2AO_realHilbert_rankOne_topOrthogonal_normalized_apply_norm_le
    R e u
    (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_norm H N)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_norm
      H N hN beta hbeta)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_eigen
      H N hN beta hbeta)
    delta hPert hSmall' x hx
  simpa only [R, delta, mul_assoc,
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator] using h

/-- Weak-coupling physical Wilson top sector: every fixed state lies in the
ONE actual top eigenline, not merely in a chosen proxy vacuum line. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalNormalizedWilson_topFixed_eq_scalar
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hStrict : 4 *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
      beta < 1)
    (x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (hx : periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta x = x) :
    ∃ c : ℝ, x = c •
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
        H N hN beta hbeta := by
  let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
    H N hN beta hbeta
  let q := 4 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H * beta
  have hOrth : ∀ y : _, inner ℝ u y = 0 → ‖S y‖ ≤ q * ‖y‖ := by
    intro y hy
    exact periodicHypercubicEvenSpecialUnitaryPhysicalNormalizedWilson_topVectorOrthogonal_norm_le_actionBudget
      H N hN beta hbeta (le_of_lt hStrict) y hy
  exact p4Q2AP_realHilbert_fixed_eq_scalar_of_orthogonal_contraction
    S u
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_norm
      H N hN beta hbeta)
    (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_vacuum_fixed
      H N hN beta hbeta)
    q hStrict hOrth x hx

/-- The canonical full top eigenspace of the ACTUAL SU(N) physical Wilson
transfer is one-dimensional in the explicit finite-H weak-coupling window. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_eq_span_weakBeta
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hStrict : 4 *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
      beta < 1) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
      H N hN beta hbeta =
      ℝ ∙ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
        H N hN beta hbeta := by
  apply le_antisymm
  · intro x hx
    have hxFix := (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_mem
      H N hN beta hbeta x).mp hx
    obtain ⟨c, hc⟩ :=
      periodicHypercubicEvenSpecialUnitaryPhysicalNormalizedWilson_topFixed_eq_scalar
        H N hN beta hbeta hStrict x hxFix
    exact Submodule.mem_span_singleton.mpr ⟨c, hc.symm⟩
  · intro x hx
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
    apply (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_mem
      H N hN beta hbeta x).mpr
    rw [← hc, map_smul,
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_vacuum_fixed
        H N hN beta hbeta]

/-- The canonical full-top spectral projection is the genuine physical
beta-top rank-one projection in this explicit finite-volume window. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection_eq_rankOne_weakBeta
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hStrict : 4 *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
      beta < 1) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
      H N hN beta hbeta =
      InnerProductSpace.rankOne ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector H N hN beta hbeta)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector H N hN beta hbeta) := by
  let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
    H N hN beta hbeta
  have hLine : realHilbertTopEigenspace S = ℝ ∙ u :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_eq_span_weakBeta
      H N hN beta hbeta hStrict
  change (realHilbertTopEigenspace S).starProjection =
    InnerProductSpace.rankOne ℝ u u
  exact p4Q2AP_realHilbert_starProjection_eq_rankOne_of_eq_span
    (realHilbertTopEigenspace S) u
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_norm
      H N hN beta hbeta) hLine

/-- The actual canonical top-sector projection differs from beta=0 Haar
rank-one by at most 2*C_H*beta ON EVERY beta-top physical state. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection_HaarLeakage_onTop
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (hxTop : x ∈ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
      H N hN beta hbeta) :
    ‖(periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
        H N hN beta hbeta -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN 0 (by norm_num)) x‖ ≤
      (2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        beta) * ‖x‖ := by
  let R := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let Q := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN 0 (by norm_num)
  let e := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N
  let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
    H N hN beta hbeta
  let delta := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H * beta
  have hPos : 0 < ‖R‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H N hN beta hbeta
  have hxFix : S x = x :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_mem
      H N hN beta hbeta x).mp hxTop
  have hEig : R x = ‖R‖ • x := by
    have hh : (‖R‖⁻¹ • R) x = x := hxFix
    have ht := congrArg (fun z : _ => ‖R‖ • z) hh
    change ‖R‖ • (‖R‖⁻¹ • R x) = ‖R‖ • x at ht
    simpa [smul_smul, mul_inv_cancel₀ hPos.ne'] using ht
  have hPert : ‖R - InnerProductSpace.rankOne ℝ e e‖ ≤ delta := by
    have h := periodicHypercubicEvenSpecialUnitaryPhysicalRawWilson_norm_sub_betaZero_le_actionBudget
      H N hN beta hbeta
    simpa only [R, e, delta,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_zero_eq_rankOne
        H N hN] using h
  have hLeak := p4Q2AP_realHilbert_rawTop_eigen_HaarProjection_le
    R e x
    (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_norm H N)
    hEig delta hPert
  have hPx : P x = x := by
    change realHilbertTopEigenspaceProjection S x = x
    exact (realHilbertTopEigenspaceProjection_apply_eq_self_iff S x).mpr hxFix
  have hQ : Q = InnerProductSpace.rankOne ℝ e e :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_zero_eq_rankOne
      H N hN
  change ‖(P - Q) x‖ ≤
    (2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
      beta) * ‖x‖
  rw [ContinuousLinearMap.sub_apply, hPx, hQ]
  simpa only [delta, mul_assoc] using hLeak

end
end MathlibAnalytic
end MGAP4D
