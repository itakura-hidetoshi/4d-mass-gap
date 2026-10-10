import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarWeakBetaSimpleTopProjection
import Mathlib.Tactic

/-!
# P4-Q2-AQ: FULL operator-norm stability of actual Wilson top spectral projection

AP proved the actual finite-volume Wilson beta-dependent top eigenspace is a
single real eigenline in its explicit small-beta regime and bounded the
canonical full-top projection minus the exact Haar rank-one endpoint ON that
top sector. Here we pass to the entire original Gauss-law physical Hilbert
space, without restricting inputs to a chosen excited or receiver space.

Let R_beta be the genuinely unnormalized one-slab Wilson Haar-L² operator,
S_beta = ‖R_beta‖⁻¹ • R_beta its normalized physical operator, and P_beta
Mathlib's canonical orthogonal projection onto the FULL eigenvalue-one space.
Let Q = R_0 be the ACTUAL beta-zero Haar rank-one Wilson transfer.

The exact global Wilson plaquette/link budget C_H provides
  ‖R_beta - Q‖ ≤ C_H beta,  ‖Q‖ = 1.
From normalization (not a synthetic transfer), we prove for ALL beta >= 0
  ‖S_beta - Q‖ ≤ 2 C_H beta.
Combining this with AO's genuine full-top-orthogonal estimate under
4 C_H beta <= 1 gives the NEW global Hilbert-space projection inequality
  ‖P_beta - Q‖ ≤ 6 C_H beta.
It follows in particular that the canonical top projections P_beta and P_0
are close in the FULL operator norm and P_0 is exactly the original Haar
projection for every SU(N) physical finite volume.

No beta>0 volume-uniform spectral/mass gap is inferred: C_H explicitly
counts finite-volume spatial plaquettes and temporal crossing links.
No proxy Gram/transfer, posterior receiver or new axiom is used.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped InnerProductSpace InnerProduct

noncomputable section
set_option maxHeartbeats 2600000
set_option synthInstance.maxHeartbeats 850000

/-- Normalizing a genuine nonzero Hilbert operator by its norm changes it
by at most the distance from an operator of norm one. Together with the
original perturbation this yields the factor two in operator norm. -/
theorem p4Q2AQ_realHilbert_normNormalized_sub_unitEndpoint_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (R Q : E →L[ℝ] E)
    (hRPos : 0 < ‖R‖) (hQNorm : ‖Q‖ = 1)
    (delta : ℝ) (hPert : ‖R - Q‖ ≤ delta) :
    ‖(‖R‖⁻¹ • R) - Q‖ ≤ 2 * delta := by
  let S : E →L[ℝ] E := ‖R‖⁻¹ • R
  have hSNorm : ‖S‖ = 1 := by
    dsimp [S]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hRPos]
    exact inv_mul_cancel₀ hRPos.ne'
  have hRScale : ‖R‖ • S = R := by
    dsimp [S]
    rw [smul_smul, mul_inv_cancel₀ hRPos.ne', one_smul]
  have hNormDelta : |1 - ‖R‖| ≤ delta := by
    have hAbs : |‖R‖ - ‖Q‖| ≤ delta :=
      (abs_norm_sub_norm_le R Q).trans hPert
    rw [hQNorm] at hAbs
    simpa only [abs_sub_comm] using hAbs
  have hSub : S - R = (1 - ‖R‖) • S := by
    calc
      S - R = (1 : ℝ) • S - ‖R‖ • S := by rw [one_smul, hRScale]
      _ = (1 - ‖R‖) • S := by rw [sub_smul]
  have hRaw : ‖S - R‖ ≤ delta := by
    rw [hSub, norm_smul, Real.norm_eq_abs, hSNorm, mul_one]
    exact hNormDelta
  change ‖S - Q‖ ≤ 2 * delta
  calc
    ‖S - Q‖ = ‖(S - R) + (R - Q)‖ := by congr 1; abel
    _ ≤ ‖S - R‖ + ‖R - Q‖ := norm_add_le _ _
    _ ≤ delta + delta := add_le_add hRaw hPert
    _ = 2 * delta := by ring

/-- Global top projection comparison from the genuine centered transfer and
the genuine original Wilson kernel, without a beta-top input restriction. -/
theorem p4Q2AQ_realHilbert_globalProjection_norm_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S P Q : E →L[ℝ] E) (delta : ℝ)
    (hCentered : ‖S - P‖ ≤ 4 * delta)
    (hEndpoint : ‖S - Q‖ ≤ 2 * delta) :
    ‖P - Q‖ ≤ 6 * delta := by
  calc
    ‖P - Q‖ = ‖(P - S) + (S - Q)‖ := by congr 1; abel
    _ ≤ ‖P - S‖ + ‖S - Q‖ := norm_add_le _ _
    _ = ‖S - P‖ + ‖S - Q‖ := by rw [norm_sub_rev]
    _ ≤ 4 * delta + 2 * delta := add_le_add hCentered hEndpoint
    _ = 6 * delta := by ring

local instance p4AQGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4AQCompact (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4AQSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4AQMeasurable (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4AQBorel (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4AQLinks (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance p4AQComplete (H N : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H N).completeSpace_coe

/-- Actual normalized Wilson physical transfer is uniformly close in
operator norm to its exact beta-zero Haar kernel for every beta >= 0.
Only the explicit finite-H local plaquette/link budget enters. -/
theorem periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_norm_sub_HaarZero_le
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN 0 (by norm_num)‖ ≤
      2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        beta := by
  let R := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let Q := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN 0 (by norm_num)
  let delta := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H * beta
  have hRPos : 0 < ‖R‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H N hN beta hbeta
  have hQNorm : ‖Q‖ = 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_zero_norm
      H N hN
  have hPert : ‖R - Q‖ ≤ delta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalRawWilson_norm_sub_betaZero_le_actionBudget
      H N hN beta hbeta
  have h := p4Q2AQ_realHilbert_normNormalized_sub_unitEndpoint_le
    R Q hRPos hQNorm delta hPert
  simpa only [R, Q, delta,
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator,
    mul_assoc] using h

/-- AQ: genuinely GLOBAL operator-norm stability of the canonical full top
spectral projection of the finite SU(N) Wilson gauge-invariant physical
transfer, compared to the actual Haar rank-one physical kernel at beta=0.
No restriction to top input vectors, no surrogate projection. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection_norm_sub_HaarZero_le
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hSmall : 4 *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
          beta ≤ 1) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
        H N hN beta hbeta -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN 0 (by norm_num)‖ ≤
      6 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        beta := by
  let R := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
    H N hN beta hbeta
  let Q := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN 0 (by norm_num)
  let delta := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H * beta
  have hSym :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
      H N hN beta hbeta
  have hCentered : ‖S - P‖ ≤ 4 * delta := by
    have heq :
        ‖S - P‖ =
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
            H N hN beta hbeta‖ := by
      simpa [S, P,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator] using
        (realHilbertCenteredOperator_norm_eq_orthogonalRestriction S hSym)
    rw [heq]
    have hb := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopOrthogonal_norm_le_actionBudget
      H N hN beta hbeta hSmall
    simpa only [delta, mul_assoc] using hb
  have hEndpoint : ‖S - Q‖ ≤ 2 * delta := by
    have h := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_norm_sub_HaarZero_le
      H N hN beta hbeta
    simpa only [S, Q, delta, mul_assoc] using h
  have hGlobal := p4Q2AQ_realHilbert_globalProjection_norm_le
    S P Q delta hCentered hEndpoint
  simpa only [P, Q, delta, mul_assoc] using hGlobal

/-- At beta zero, the original physical Haar transfer is EXACTLY the
full-top orthogonal projection at every finite SU(N) spatial volume. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection_betaZero_eq_Haar
    (H N : ℕ) (hN : 0 < N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
        H N hN 0 (by norm_num) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN 0 (by norm_num) := by
  let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
    H N hN 0 (by norm_num)
  let Q := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN 0 (by norm_num)
  have hBound : ‖P - Q‖ ≤ 0 := by
    simpa [P, Q] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection_norm_sub_HaarZero_le
        H N hN 0 (by norm_num) (by simp))
  have hZeroNorm : ‖P - Q‖ = 0 :=
    le_antisymm hBound (norm_nonneg _)
  have hZero : P - Q = 0 :=
    (ContinuousLinearMap.opNorm_zero_iff (P - Q)).mp hZeroNorm
  exact sub_eq_zero.mp hZero

/-- The actual beta-dependent and beta-zero full top spectral projections
are globally close in the genuine physical Hilbert operator norm. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection_norm_sub_betaZero_le
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hSmall : 4 *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
          beta ≤ 1) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
        H N hN beta hbeta -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
        H N hN 0 (by norm_num)‖ ≤
      6 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        beta := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection_betaZero_eq_Haar]
  exact periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection_norm_sub_HaarZero_le
    H N hN beta hbeta hSmall

end
end MathlibAnalytic
end MGAP4D
