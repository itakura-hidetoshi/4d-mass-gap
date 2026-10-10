import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaLipschitz
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaZeroRankOne
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalRawKernelDirichlet
import Mathlib.Tactic

/-!
# P4-Q2-AN: genuine Wilson local-action Dirichlet bound near beta zero

The ACTUAL one-slab physical transfer R_beta (not a posterior receiver or
proxy Gram) is controlled using its literal Wilson kernel and its
plaquette/link action-count constant C_H.  At beta=0 the physical transfer
is the exact Haar-constant rank-one projection R_0.

For a genuine Gauss-law physical state f orthogonal to the Haar constant,
the raw transfer obeys ‖R_beta f‖ ≤ C_H beta ‖f‖. Combining the literal
Wilson-kernel Lipschitz estimate with ‖R_0‖=1 yields the NONTRIVIAL
finite-volume Dirichlet lower bound

  (1 - 2 C_H beta) ‖f‖² ≤ ‖R_beta‖² ‖f‖² - ‖R_beta f‖²

whenever 2 C_H beta ≤ 1, and strict positivity if 2 C_H beta < 1 and
f ≠ 0.  The finite-H action constant is explicitly the genuine Wilson
plaquette/link count; it grows with volume and this does NOT prove a
volume-uniform beta>0 gap, the beta-dependent top-sector excited gap,
or any continuum mass gap.

The Haar-constant-orthogonal sector is not silently identified with the
beta-dependent entire top-eigenspace complement of P4-Q2-AM.
No new axioms, sorry, admits, or surrogate physical operators.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section
set_option maxHeartbeats 2600000
set_option synthInstance.maxHeartbeats 850000

/-- An endpoint rank-one annihilation and a genuine perturbation norm
control imply a quadratic raw Dirichlet lower bound.  This generic
algebraic bridge is specialized BELOW to the literal Wilson action. -/
theorem p4Q2AN_realHilbert_endpointPerturbation_rawDirichlet_lower
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (R R0 : E →L[ℝ] E) (x : E)
    (hR0norm : ‖R0‖ = 1) (hR0x : R0 x = 0)
    (delta : ℝ) (hdelta : 0 ≤ delta)
    (hPert : ‖R - R0‖ ≤ delta)
    (hWindow : 2 * delta ≤ 1) :
    (1 - 2 * delta) * ‖x‖ ^ 2 ≤
      ‖R‖ ^ 2 * ‖x‖ ^ 2 - ‖R x‖ ^ 2 := by
  have hNormDiff : |‖R‖ - ‖R0‖| ≤ delta :=
    (abs_norm_sub_norm_le R R0).trans hPert
  have hNormLeft : -delta ≤ ‖R‖ - ‖R0‖ :=
    (abs_le.mp hNormDiff).1
  have hRLower : 1 - delta ≤ ‖R‖ := by
    rw [hR0norm] at hNormLeft
    linarith
  have hAction : ‖R x‖ ≤ delta * ‖x‖ := by
    calc
      ‖R x‖ = ‖(R - R0) x‖ := by
        simp only [ContinuousLinearMap.sub_apply, hR0x, sub_zero]
      _ ≤ ‖R - R0‖ * ‖x‖ := (R - R0).le_opNorm x
      _ ≤ delta * ‖x‖ :=
        mul_le_mul_of_nonneg_right hPert (norm_nonneg x)
  have hOneLower : 0 ≤ 1 - delta := by linarith
  have hNormSq : (1 - delta) ^ 2 ≤ ‖R‖ ^ 2 :=
    (sq_le_sq₀ hOneLower (norm_nonneg R)).mpr hRLower
  have hActionSq : ‖R x‖ ^ 2 ≤ (delta * ‖x‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg (R x))
      (mul_nonneg hdelta (norm_nonneg x))).mpr hAction
  have hMul := mul_le_mul_of_nonneg_right hNormSq (sq_nonneg ‖x‖)
  calc
    (1 - 2 * delta) * ‖x‖ ^ 2 =
        (1 - delta) ^ 2 * ‖x‖ ^ 2 - (delta * ‖x‖) ^ 2 := by ring
    _ ≤ ‖R‖ ^ 2 * ‖x‖ ^ 2 - ‖R x‖ ^ 2 := by
      linarith

local instance p4ANGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4ANCompact (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4ANSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4ANMeasurable (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4ANBorel (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4ANLinks (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance p4ANComplete (H N : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H N).completeSpace_coe

/-- Beta-zero anchoring of the ACTUAL raw physical Wilson transfer in
operator norm, using the existing exact one-slab Haar kernel bound. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalRawWilson_norm_sub_betaZero_le_actionBudget
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN 0 (by norm_num)‖ ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        beta := by
  simpa [Real.norm_eq_abs, abs_of_nonneg hbeta] using
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_sub_le_beta
      H N hN 0 beta (by norm_num) hbeta)

/-- ACTUAL physical Wilson kernel damping of any Haar-mean-zero input.
No change from the physical Gauss-law source Hilbert space is made. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalRawWilson_HaarCentered_apply_norm_le
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (hHaar : inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) f = 0) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta f‖ ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        beta) * ‖f‖ := by
  let R := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let R0 := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN 0 (by norm_num)
  have hZero : R0 f = 0 := by
    change periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN 0 (by norm_num) f = 0
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_zero_apply,
      hHaar, zero_smul]
  have hPert : ‖R - R0‖ ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        beta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalRawWilson_norm_sub_betaZero_le_actionBudget
      H N hN beta hbeta
  change ‖R f‖ ≤
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
      beta) * ‖f‖
  calc
    ‖R f‖ = ‖(R - R0) f‖ := by
      simp only [ContinuousLinearMap.sub_apply, hZero, sub_zero]
    _ ≤ ‖R - R0‖ * ‖f‖ := (R - R0).le_opNorm f
    _ ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        beta) * ‖f‖ :=
      mul_le_mul_of_nonneg_right hPert (norm_nonneg f)

/-- Explicit positive-beta finite-volume Dirichlet lower bound, sourced
directly from the literal Wilson plaquette/link action constant and the
rank-one beta-zero physical Haar endpoint. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalRawWilson_HaarCentered_dirichlet_lower
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (hHaar : inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) f = 0)
    (hWindow : 2 *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
          beta ≤ 1) :
    (1 - 2 *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        beta) * ‖f‖ ^ 2 ≤
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖ ^ 2 * ‖f‖ ^ 2 -
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta f‖ ^ 2 := by
  let R := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let R0 := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN 0 (by norm_num)
  let delta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H * beta
  have hR0norm : ‖R0‖ = 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_zero_norm
      H N hN
  have hR0f : R0 f = 0 := by
    change periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN 0 (by norm_num) f = 0
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_zero_apply,
      hHaar, zero_smul]
  have hDelta : 0 ≤ delta := mul_nonneg
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget_nonneg H)
    hbeta
  have hPert : ‖R - R0‖ ≤ delta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalRawWilson_norm_sub_betaZero_le_actionBudget
      H N hN beta hbeta
  have hSmall : 2 * delta ≤ 1 := by
    dsimp [delta]
    nlinarith [hWindow]
  simpa only [delta, mul_assoc] using
    (p4Q2AN_realHilbert_endpointPerturbation_rawDirichlet_lower
      R R0 f hR0norm hR0f delta hDelta hPert hSmall)

/-- Strict raw Wilson Dirichlet positivity for every nonzero Haar-centered
physical vector throughout the explicit finite-H weak-coupling window. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalRawWilson_HaarCentered_dirichlet_pos
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (hHaar : inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) f = 0)
    (hf : f ≠ 0)
    (hWindow : 2 *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
          beta < 1) :
    0 <
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖ ^ 2 * ‖f‖ ^ 2 -
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta f‖ ^ 2 := by
  have hLower :=
    periodicHypercubicEvenSpecialUnitaryPhysicalRawWilson_HaarCentered_dirichlet_lower
      H N hN beta hbeta f hHaar (le_of_lt hWindow)
  have hFactor : 0 < 1 - 2 *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        beta := by
    linarith
  have hfpos : 0 < ‖f‖ := norm_pos_iff.mpr hf
  exact lt_of_lt_of_le (mul_pos hFactor (pow_pos hfpos 2)) hLower

end
end MathlibAnalytic
end MGAP4D
