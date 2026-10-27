import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFullLinkGLCancellationKrylovRayleighV5_PZ37ZH
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarFullTopProjectionNormStability
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ZI — explicit actual-Wilson full-link GL O(t²) fine envelope

This module closes a previously unquantified part of the genuine fine-zero
GL cancellation limit without replacing ANY physical or posterior structure.

The exact normalized SU(2) Wilson one-slab physical operator T_t and its
Haar rank-one endpoint T_0 satisfy the original AQ operator-norm estimate

    ||T_t - T_0|| <= 2 B_H t,

where B_H is the literal finite-H Wilson spatial-plaquette and temporal
crossing-action budget, not a surrogate or uniform-in-H constant.

For the actual Gauss-law Hilbert cancellation F_t=U-T_t U, and the exact
TWO INTERACTING original Wilson posterior density-contrast variance
integrated over ALL spatial links and physical Haar boundary pairs, prove

    ||F_t|| <= 2 B_H t,
    0 <= M_GL(H,b;F_t) <= C_GL(H,b) (2 B_H t)^2,
    C_GL(H,b) = 2 |Links(H)| / exp(-16b).

The bound is genuinely quadratic in the positive fine parameter for every
finite H, not merely a fixed-volume continuity limit. PZ37ZH establishes
strict positivity of M_GL and of the physical source-normalized GL Rayleigh
for sufficiently small positive t, compatible with this O(t²) absolute mass.

A two-sided physical slope and the asymptotic direction F_t/||F_t||
are NOT asserted here: the first-order variation of the raw Wilson Haar
row (JG) does not itself supply differentiability of the OPERATOR-NORM
normalizer. This distinction is essential for the subsequent transverse
source-tangent analysis. No positive H/fine-uniform source coercivity,
endpoint E, all-depth F, H1-H4 or continuum Yang--Mills mass gap.
No new axiom, sorry, admit, native_decide, Dobrushin or proxy posterior.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37ZI_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ZI_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ZI_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ZI_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ZI_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2PZ37ZI_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Exact finite-H original SU(2) Wilson one-slab action budget. It
counts genuine spatial plaquette and temporal crossing contributions. -/
noncomputable def p4Q2PZ37ZI_originalPhysicalWilsonActionBudget (H : ℕ) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H

/-- Use AQ's original Wilson normalized-transfer perturbation and the
EXACT Haar rank-one transfer at t=0. The finite-volume coefficient
depends only on the original physical one-slab Wilson action budget. -/
theorem p4Q2PZ37ZI_originalNormalizedTransfer_distance_le_actionBudget
    (H : ℕ) (t : Set.Ici (0 : ℝ)) :
    ‖periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperatorHalfLine
        H 2 specialUnitaryTwoWilsonRankPositive t -
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperatorHalfLine
        H 2 specialUnitaryTwoWilsonRankPositive
          (⟨0, le_refl (0 : ℝ)⟩ : Set.Ici (0 : ℝ))‖ ≤
      2 * p4Q2PZ37ZI_originalPhysicalWilsonActionBudget H * (t : ℝ) := by
  have hAQ :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_norm_sub_HaarZero_le
      H 2 specialUnitaryTwoWilsonRankPositive (t : ℝ) t.property
  change
    ‖periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        H 2 specialUnitaryTwoWilsonRankPositive (t : ℝ) t.property -
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        H 2 specialUnitaryTwoWilsonRankPositive 0 (by norm_num)‖ ≤
      2 * p4Q2PZ37ZI_originalPhysicalWilsonActionBudget H * (t : ℝ)
  rw [periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_zero_eq
    H 2 specialUnitaryTwoWilsonRankPositive]
  simpa only [p4Q2PZ37ZI_originalPhysicalWilsonActionBudget] using hAQ

/-- Genuine Gauss-law Hilbert physical cancellation is O_H(t), with the
explicit ORIGINAL Wilson action budget, at all nonnegative fine t. -/
theorem p4Q2PZ37ZI_originalPhysicalCancellation_norm_le_linearFine
    (H : ℕ) (t : Set.Ici (0 : ℝ)) :
    ‖p4Q2PZ37ZE_originalPhysicalCancellation H t‖ ≤
      2 * p4Q2PZ37ZI_originalPhysicalWilsonActionBudget H * (t : ℝ) := by
  let T :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperatorHalfLine
      H 2 specialUnitaryTwoWilsonRankPositive
  let t0 : Set.Ici (0 : ℝ) := ⟨0, le_refl (0 : ℝ)⟩
  let U := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  have hZero : T t0 U = U := by
    simp [T, t0, U]
  have hSource :
      p4Q2PZ37ZE_originalPhysicalCancellation H t =
        -((T t - T t0) U) := by
    change U - T t U = -((T t - T t0) U)
    rw [ContinuousLinearMap.sub_apply, hZero]
    abel
  have hUNorm : ‖U‖ = (1 : ℝ) :=
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_norm H 2
  have hDist :=
    p4Q2PZ37ZI_originalNormalizedTransfer_distance_le_actionBudget H t
  calc
    ‖p4Q2PZ37ZE_originalPhysicalCancellation H t‖ =
        ‖(T t - T t0) U‖ := by rw [hSource, norm_neg]
    _ ≤ ‖T t - T t0‖ * ‖U‖ := (T t - T t0).le_opNorm U
    _ = ‖T t - T t0‖ := by rw [hUNorm, mul_one]
    _ ≤ 2 * p4Q2PZ37ZI_originalPhysicalWilsonActionBudget H * (t : ℝ) := hDist

/-- Original FULL LINK/BOUNDARY two-interacting Wilson posterior GL mass
has a TRUE explicit O_H,b(t²) upper envelope on the cancellation source
for the ENTIRE nonnegative fine half-line, not only a local asymptotic. -/
theorem p4Q2PZ37ZI_originalFullLinkGLMass_le_quadraticFineBudget
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (t : Set.Ici (0 : ℝ)) :
    0 ≤ p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
        H b (le_of_lt hb) (p4Q2PZ37ZE_originalPhysicalCancellation H t)
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) ∧
    p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
        H b (le_of_lt hb) (p4Q2PZ37ZE_originalPhysicalCancellation H t)
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) ≤
      p4Q2PZ37ZG_originalFullLinkGL_RayleighCap H b *
        (2 * p4Q2PZ37ZI_originalPhysicalWilsonActionBudget H * (t : ℝ)) ^ 2 := by
  have hSource :=
    p4Q2PZ37ZI_originalPhysicalCancellation_norm_le_linearFine H t
  have hSquare :
      ‖p4Q2PZ37ZE_originalPhysicalCancellation H t‖ ^ 2 ≤
        (2 * p4Q2PZ37ZI_originalPhysicalWilsonActionBudget H * (t : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hSource 2
  have hCap : 0 ≤ p4Q2PZ37ZG_originalFullLinkGL_RayleighCap H b := by
    unfold p4Q2PZ37ZG_originalFullLinkGL_RayleighCap
    positivity
  have hUpper :=
    p4Q2PZ37ZC_originalGL_fullLink_le_explicit_physicalSourceNorm
      H b hb (p4Q2PZ37ZE_originalPhysicalCancellation H t)
  constructor
  · exact p4Q2PZ37ZG_originalGL_fullLink_nonneg
      H b hb (p4Q2PZ37ZE_originalPhysicalCancellation H t)
  · calc
      p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
          H b (le_of_lt hb) (p4Q2PZ37ZE_originalPhysicalCancellation H t)
          (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) ≤
        ((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
          (2 * ‖p4Q2PZ37ZE_originalPhysicalCancellation H t‖ ^ 2)) /
            Real.exp (-16 * b) := hUpper
      _ = p4Q2PZ37ZG_originalFullLinkGL_RayleighCap H b *
          ‖p4Q2PZ37ZE_originalPhysicalCancellation H t‖ ^ 2 := by
        unfold p4Q2PZ37ZG_originalFullLinkGL_RayleighCap
        ring
      _ ≤ p4Q2PZ37ZG_originalFullLinkGL_RayleighCap H b *
            (2 * p4Q2PZ37ZI_originalPhysicalWilsonActionBudget H * (t : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_left hSquare hCap

/-- The GL numerator genuinely decays at least QUADRATICALLY in fine t,
yet is STRICTLY POSITIVE at every sufficiently small positive fine.
This does not determine the limiting source-normalized Rayleigh ratio. -/
theorem p4Q2PZ37ZI_positiveFine_strictGLMass_with_quadraticEnvelope
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (left₀ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ t : Set.Ici (0 : ℝ),
        0 < (t : ℝ) → (t : ℝ) < delta →
        0 < p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
          H b (le_of_lt hb) (p4Q2PZ37ZE_originalPhysicalCancellation H t)
          (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) ∧
        p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
          H b (le_of_lt hb) (p4Q2PZ37ZE_originalPhysicalCancellation H t)
          (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) ≤
        p4Q2PZ37ZG_originalFullLinkGL_RayleighCap H b *
          (2 * p4Q2PZ37ZI_originalPhysicalWilsonActionBudget H * (t : ℝ)) ^ 2 := by
  obtain ⟨delta, hDelta, hNonzero⟩ :=
    p4Q2PZ37ZF_originalPhysicalCancellation_ne_zero_smallPositive H
  refine ⟨delta, hDelta, ?_⟩
  intro t ht hSmall
  exact ⟨p4Q2PZ37ZH_originalGLMass_pos_of_physicalCancellation_ne_zero
    H b hb e left₀ t (hNonzero t ht hSmall),
    (p4Q2PZ37ZI_originalFullLinkGLMass_le_quadraticFineBudget H b hb t).2⟩

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZI_originalNormalizedTransfer_distance_le_actionBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZI_originalPhysicalCancellation_norm_le_linearFine
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZI_originalFullLinkGLMass_le_quadraticFineBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZI_positiveFine_strictGLMass_with_quadraticEnvelope
