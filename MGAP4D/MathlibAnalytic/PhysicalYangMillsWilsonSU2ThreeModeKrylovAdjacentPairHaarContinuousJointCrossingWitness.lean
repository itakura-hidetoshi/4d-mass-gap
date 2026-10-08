import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarConcretePositiveBetaCrossingWitness
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumFiberDistortion
import Mathlib.Tactic

/-!
# P4: an everywhere-positive continuous representative of the genuine Wilson joint law

PR #5295 constructs, in EVERY finite SU(2) even-periodic spatial
volume at EVERY beta>0, explicit physical boundaries A and B with
the original temporal one-slab Wilson kernel minor strictly positive.

The ORIGINAL physical top eigenvector is an L2 class; one cannot
legitimately evaluate its arbitrary quotient representative at A,B.
This file instead uses the ALREADY-CONSTRUCTED canonical continuous
top-vacuum representative Ω_c, which:
  1. is STRICTLY positive at EVERY spatial boundary configuration;
  2. agrees almost everywhere with the ORIGINAL nonnegative top
     eigenvector under the ORIGINAL spatial Haar law.

The genuine normalized Wilson joint density thus has the canonical
continuous-version formula

  W_c(A,B) = lambda_beta^(-1) Ω_c(A) K_beta(A,B) Ω_c(B).

We prove this differs from the existing original Wilson joint
normalized-weight function only on a pair-Haar null set, using the
actual joint half-density, norm and original Wilson kernel unchanged.

Because the canonical Ω_c is pointwise positive, the two-by-two
minor of W_c at the concrete #5295 boundaries is STRICTLY POSITIVE
at every positive coupling, and no pointwise left/right factorization
of this CONTINUOUS representative is possible.

This is strictly stronger than the conditional representative-value
hypotheses of #5293/5294, and carefully DOES NOT replace the
arbitrary old L2 quotient representative pointwise.
Transfer to almost-everywhere conditional-posterior obstruction
and positive-beta volume-uniform bounds remain distinct tasks.
No Dobrushin or continuum mass-gap claim.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance p4CanonicalVacuumTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4CanonicalVacuumCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4CanonicalVacuumSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4CanonicalVacuumMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4CanonicalVacuumBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4CanonicalVacuumSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance p4CanonicalVacuumSpatialHaarProbability (H : ℕ) :
    IsProbabilityMeasure (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint

/-- The exact original Wilson joint density, expressed using the
canonical continuous physical top vacuum rather than the arbitrary
pointwise representative of the pre-existing L2 quotient. -/
noncomputable def originalWilsonContinuousPhysicalJointWeight
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) : ℝ :=
  ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H 2 (by norm_num) beta hbeta‖⁻¹ *
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
      H 2 (by norm_num) beta hbeta z.1 *
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
      H 2 beta z.1 z.2 *
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
      H 2 (by norm_num) beta hbeta z.2

/-- The concrete continuous-version Wilson joint density is
almost everywhere EXACTLY the original physical ground-state
normalized weight on the ORIGINAL ordered pair-Haar law.
No fictional replacement or pointwise L2 equality is invoked. -/
theorem originalWilsonContinuousPhysicalJointWeight_ae_eq_original
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    (fun z => originalWilsonContinuousPhysicalJointWeight H beta hbeta z) =ᵐ[
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).prod
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)]
      (fun z =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
          H 2 (by norm_num) beta hbeta z) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let ω := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
    H 2 (by norm_num) beta hbeta
  let ω₀ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 → ℝ :=
    fun B => (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
      H 2 (by norm_num) beta hbeta).1 B
  have hω : ω =ᵐ[μ] ω₀ := by
    exact periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_ae_eq_existing
      H 2 (by norm_num) beta hbeta
  have hfst :
      (fun z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 => ω z.1)
        =ᵐ[μ.prod μ] (fun z => ω₀ z.1) := by
    simpa [Function.comp_def] using
      (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae_eq hω
  have hsnd :
      (fun z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 => ω z.2)
        =ᵐ[μ.prod μ] (fun z => ω₀ z.2) := by
    simpa [Function.comp_def] using
      (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae_eq hω
  change (fun z => originalWilsonContinuousPhysicalJointWeight H beta hbeta z)
      =ᵐ[μ.prod μ]
    (fun z => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
      H 2 (by norm_num) beta hbeta z)
  filter_upwards [hfst, hsnd] with z hz₁ hz₂
  change
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) beta hbeta‖⁻¹ *
      ω z.1 *
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta z.1 z.2 *
      ω z.2 =
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) beta hbeta‖⁻¹ *
      ω₀ z.1 *
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta z.1 z.2 *
      ω₀ z.2
  rw [hz₁, hz₂]

/-- Exact full two-by-two determinant of the new CANONICAL CONTINUOUS
representative of the SAME original physical Wilson joint law. -/
noncomputable def originalWilsonContinuousPhysicalJointTwoByTwoMinor
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (A₁ A₂ B₁ B₂ :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) : ℝ :=
  originalWilsonContinuousPhysicalJointWeight H beta hbeta (A₁, B₁) *
    originalWilsonContinuousPhysicalJointWeight H beta hbeta (A₂, B₂) -
  originalWilsonContinuousPhysicalJointWeight H beta hbeta (A₁, B₂) *
    originalWilsonContinuousPhysicalJointWeight H beta hbeta (A₂, B₁)

/-- Exact cancellation of all four canonical vacuum factors,
without assuming equal values at arbitrary points of an L2 class. -/
theorem originalWilsonContinuousPhysicalJointTwoByTwoMinor_factor
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (A₁ A₂ B₁ B₂ :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    originalWilsonContinuousPhysicalJointTwoByTwoMinor H beta hbeta A₁ A₂ B₁ B₂ =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H 2 (by norm_num) beta hbeta‖⁻¹ ^ 2 *
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H 2 (by norm_num) beta hbeta A₁ *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H 2 (by norm_num) beta hbeta A₂ *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H 2 (by norm_num) beta hbeta B₁ *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H 2 (by norm_num) beta hbeta B₂) *
      originalWilsonTemporalKernelTwoByTwoMinor H 2 beta A₁ A₂ B₁ B₂ := by
  unfold originalWilsonContinuousPhysicalJointTwoByTwoMinor
    originalWilsonContinuousPhysicalJointWeight
    originalWilsonTemporalKernelTwoByTwoMinor
  ring

/-- Explicit positive-beta strict crossing minor of the canonical
CONTINUOUS physical Wilson joint density, for every spatial H. -/
theorem originalWilsonContinuousPhysicalJoint_explicitMinor_pos
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta) :
    0 < originalWilsonContinuousPhysicalJointTwoByTwoMinor H beta (le_of_lt hbeta)
      (originalWilsonExplicitIdentityBoundary H)
      (originalWilsonExplicitRotatedBoundary H)
      (originalWilsonExplicitIdentityBoundary H)
      (originalWilsonExplicitRotatedBoundary H) := by
  let A := originalWilsonExplicitIdentityBoundary H
  let B := originalWilsonExplicitRotatedBoundary H
  letI : Fact (0 < (2 : ℕ)) := ⟨by norm_num⟩
  have hA :
      0 < periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H 2 (by norm_num) beta (le_of_lt hbeta) A :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H 2 (by norm_num) beta (le_of_lt hbeta) A
  have hB :
      0 < periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H 2 (by norm_num) beta (le_of_lt hbeta) B :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H 2 (by norm_num) beta (le_of_lt hbeta) B
  have hT :
      0 < ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) beta (le_of_lt hbeta)‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos_from_uniform_kernel_floor
      H 2 (by norm_num) beta (le_of_lt hbeta)
  have hK : 0 < originalWilsonTemporalKernelTwoByTwoMinor H 2 beta A B A B :=
    originalWilsonExplicitBoundaries_oneSlabKernelMinor_pos H beta hbeta
  change 0 < originalWilsonContinuousPhysicalJointTwoByTwoMinor H beta
      (le_of_lt hbeta) A B A B
  rw [originalWilsonContinuousPhysicalJointTwoByTwoMinor_factor]
  exact mul_pos
    (mul_pos
      (pow_pos (inv_pos.mpr hT) 2)
      (mul_pos (mul_pos (mul_pos hA hB) hA) hB))
    hK

/-- Without any artificial nonzero physical-vacuum representative
assumptions, the canonical continuous version of the actual
positive-beta Wilson joint density is NOT a pointwise separable
left/right rank-one kernel. This does not assert that the arbitrary
old L2 quotient representative has the same value at exceptional points. -/
theorem originalWilsonContinuousPhysicalJoint_not_pointwise_separable
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta) :
    ¬ ∃ (F G : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 → ℝ),
      ∀ A B,
        originalWilsonContinuousPhysicalJointWeight H beta (le_of_lt hbeta) (A,B) =
          F A * G B := by
  intro ⟨F,G,hSep⟩
  have hpos :=
    originalWilsonContinuousPhysicalJoint_explicitMinor_pos H beta hbeta
  have hzero :
      originalWilsonContinuousPhysicalJointTwoByTwoMinor H beta (le_of_lt hbeta)
        (originalWilsonExplicitIdentityBoundary H)
        (originalWilsonExplicitRotatedBoundary H)
        (originalWilsonExplicitIdentityBoundary H)
        (originalWilsonExplicitRotatedBoundary H) = 0 := by
    unfold originalWilsonContinuousPhysicalJointTwoByTwoMinor
    rw [hSep, hSep, hSep, hSep]
    ring
  exact (ne_of_gt hpos) hzero

end GroundStatePosteriorJoint

end
end MathlibAnalytic
end MGAP4D
