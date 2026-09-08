import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumFiberDistortion
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateMarginalGeometry
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance groundStateContinuousVacuumJointIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance groundStateContinuousVacuumJointCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance groundStateContinuousVacuumJointSecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance groundStateContinuousVacuumJointMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance groundStateContinuousVacuumJointBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance groundStateContinuousVacuumJointSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Pointwise vacuum density obtained from the canonical continuous physical
vacuum representative.  Unlike the older quotient representative, this is a
genuine continuous positive function on the complete spatial boundary. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumWeight
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
    H N hN beta hbeta A) ^ 2

/-- Pointwise ground-state one-slab joint density before normalization, written
entirely with the canonical continuous physical vacuum. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateContinuousVacuumJointWeight
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
      H N hN beta hbeta z.1 *
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
      H N beta z.1 z.2 *
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
      H N hN beta hbeta z.2

/-- Normalized pointwise ground-state joint density using the canonical
continuous vacuum. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateContinuousVacuumJointNormalizedWeight
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖⁻¹ *
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateContinuousVacuumJointWeight
      H N hN beta hbeta z

/-- Vacuum boundary law presented through the pointwise continuous density. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumMeasure
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Measure (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).withDensity
    (fun A => ENNReal.ofReal
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumWeight
        H N hN beta hbeta A))

/-- Ground-state one-slab joint law presented through the canonical pointwise
continuous vacuum density. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateContinuousVacuumJointMeasure
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Measure
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N).withDensity
    (fun z => ENNReal.ofReal
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateContinuousVacuumJointNormalizedWeight
        H N hN beta hbeta z))

/-- The continuous-vacuum boundary density is continuous. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumWeight_continuous
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Continuous
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumWeight
        H N hN beta hbeta) := by
  have hΩ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_continuous
      H N hN beta hbeta
  simpa [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumWeight,
    pow_two] using hΩ.mul hΩ

/-- The continuous-vacuum boundary density is strictly positive everywhere. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumWeight_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    0 < periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumWeight
      H N hN beta hbeta A := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumWeight
  exact sq_pos_of_pos
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H N hN beta hbeta A)

/-- The raw continuous-vacuum ground-state joint density is continuous. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateContinuousVacuumJointWeight_continuous
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Continuous
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateContinuousVacuumJointWeight
        H N hN beta hbeta) := by
  have hΩ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_continuous
      H N hN beta hbeta
  have hleft := hΩ.comp continuous_fst
  have hright := hΩ.comp continuous_snd
  have hkernel :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
      H N beta
  exact (hleft.mul hkernel).mul hright

/-- The raw continuous-vacuum ground-state joint density is strictly positive
everywhere, with no exceptional representative null set. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateContinuousVacuumJointWeight_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    0 <
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateContinuousVacuumJointWeight
        H N hN beta hbeta z := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateContinuousVacuumJointWeight
  exact mul_pos
    (mul_pos
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
        H N hN beta hbeta z.1)
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
        H N beta z.1 z.2))
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H N hN beta hbeta z.2)

/-- The normalized continuous-vacuum ground-state joint density is continuous. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateContinuousVacuumJointNormalizedWeight_continuous
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Continuous
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateContinuousVacuumJointNormalizedWeight
        H N hN beta hbeta) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateContinuousVacuumJointNormalizedWeight
  exact continuous_const.mul
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateContinuousVacuumJointWeight_continuous
      H N hN beta hbeta)

/-- The normalized continuous-vacuum ground-state joint density is strictly
positive everywhere. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateContinuousVacuumJointNormalizedWeight_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    0 <
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateContinuousVacuumJointNormalizedWeight
        H N hN beta hbeta z := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateContinuousVacuumJointNormalizedWeight
  exact mul_pos
    (inv_pos.mpr
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos_from_uniform_kernel_floor
        H N hN beta hbeta))
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateContinuousVacuumJointWeight_pos
      H N hN beta hbeta z)

/-- The continuous pointwise vacuum density agrees almost everywhere with the
older quotient-representative vacuum density. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumWeight_ae_eq_existing
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumWeight
        H N hN beta hbeta =ᵐ[
      periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N]
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumWeight
        H N hN beta hbeta := by
  filter_upwards
    [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_ae_eq_existing
      H N hN beta hbeta] with A hA
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumWeight
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumWeight
  rw [hA]

/-- The continuous pointwise raw joint density agrees almost everywhere with
the existing ground-state joint density. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateContinuousVacuumJointWeight_ae_eq_existing
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateContinuousVacuumJointWeight
        H N hN beta hbeta =ᵐ[
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N]
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointWeight
        H N hN beta hbeta := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  have hΩ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_ae_eq_existing
      H N hN beta hbeta
  have hfst :
      ∀ᵐ z ∂(μ.prod μ),
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H N hN beta hbeta z.1 =
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
            H N hN beta hbeta).1 z.1 :=
    (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae hΩ
  have hsnd :
      ∀ᵐ z ∂(μ.prod μ),
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H N hN beta hbeta z.2 =
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
            H N hN beta hbeta).1 z.2 :=
    (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae hΩ
  change
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateContinuousVacuumJointWeight
        H N hN beta hbeta =ᵐ[μ.prod μ]
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointWeight
        H N hN beta hbeta
  filter_upwards [hfst, hsnd] with z hleft hright
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateContinuousVacuumJointWeight
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointWeight
  rw [hleft, hright]

/-- The normalized continuous pointwise joint density agrees almost everywhere
with the existing normalized ground-state joint density. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateContinuousVacuumJointNormalizedWeight_ae_eq_existing
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateContinuousVacuumJointNormalizedWeight
        H N hN beta hbeta =ᵐ[
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N]
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
        H N hN beta hbeta := by
  filter_upwards
    [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateContinuousVacuumJointWeight_ae_eq_existing
      H N hN beta hbeta] with z hz
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateContinuousVacuumJointNormalizedWeight
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
  rw [hz]

/-- The continuous-vacuum boundary law is exactly the already constructed
physical vacuum boundary measure. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumMeasure_eq_existing
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumMeasure
        H N hN beta hbeta =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumMeasure
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
  apply MeasureTheory.withDensity_congr_ae
  filter_upwards
    [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumWeight_ae_eq_existing
      H N hN beta hbeta] with A hA
  rw [hA]

/-- The continuous-vacuum pointwise joint law is exactly the previously
constructed ground-state joint measure.  Thus all existing joint `L²` and
conditional-expectation geometry can be read using a genuine continuous,
everywhere-positive density without changing the measure. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateContinuousVacuumJointMeasure_eq_existing
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateContinuousVacuumJointMeasure
        H N hN beta hbeta =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateContinuousVacuumJointMeasure
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
  apply MeasureTheory.withDensity_congr_ae
  filter_upwards
    [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateContinuousVacuumJointNormalizedWeight_ae_eq_existing
      H N hN beta hbeta] with z hz
  rw [hz]

/-- The continuous-vacuum boundary presentation is a probability measure. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumMeasure_isProbabilityMeasure
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumMeasure
        H N hN beta hbeta) := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumMeasure_eq_existing]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure_isProbabilityMeasure
      H N hN beta hbeta

/-- The continuous-vacuum joint presentation is a probability measure. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateContinuousVacuumJointMeasure_isProbabilityMeasure
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateContinuousVacuumJointMeasure
        H N hN beta hbeta) := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateContinuousVacuumJointMeasure_eq_existing]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_isProbabilityMeasure
      H N hN beta hbeta

/-- The right marginal of the continuous-vacuum joint presentation is exactly
the continuous-vacuum boundary law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateContinuousVacuumJointMeasure_map_snd
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Measure.map Prod.snd
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateContinuousVacuumJointMeasure
          H N hN beta hbeta) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumMeasure
        H N hN beta hbeta := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateContinuousVacuumJointMeasure_eq_existing]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumMeasure_eq_existing]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_map_snd
      H N hN beta hbeta

end

end MathlibAnalytic
end MGAP4D
