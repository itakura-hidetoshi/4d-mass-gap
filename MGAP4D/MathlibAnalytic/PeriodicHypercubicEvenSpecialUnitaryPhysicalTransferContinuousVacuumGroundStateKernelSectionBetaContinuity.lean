import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumBetaContinuity
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumGroundStateKernelSectionContinuousDensity
import MGAP4D.MathlibAnalytic.RealIntegralWeightedProbabilityContinuity

/-!
# Coupling and boundary continuity of the actual fixed-right kernel law

At fixed finite volume the existing continuous vacuum and literal Wilson kernel
have a jointly continuous product. The old and continuous weights agree on the
full left boundary Haar-almost everywhere, so their actual masses agree and are
strictly positive. The compact weighted-probability theorem then gives joint
continuity of the normalized density and expectations of varying continuous
tests. Finally the established equality of measures transfers the conclusion
to the original L2-presented law, without choosing another vacuum or law.

There is no restriction of a product-a.e. identity to arbitrary one-link fibers,
no uniform mass floor, and no response-continuity or spectral-gap assumption.
All conclusions are for N > 0 and beta >= 0, including beta = 0.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory

noncomputable section

set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 50000

local instance groundStateKernelSectionBetaContinuitySpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance groundStateKernelSectionBetaContinuitySpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance groundStateKernelSectionBetaContinuitySpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance groundStateKernelSectionBetaContinuitySpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance groundStateKernelSectionBetaContinuitySpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance groundStateKernelSectionBetaContinuitySpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Joint continuity of the literal fixed-right weight in coupling, fixed right
boundary, and integration variable. The original continuous vacuum is retained. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight_beta_joint_continuous
    (H N : ℕ) (hN : 0 < N) :
    Continuous (fun q : (Set.Ici (0 : ℝ) ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
        H N hN q.1.1.1 q.1.1.2 q.1.2 q.2) := by
  have hVacuum : Continuous
      (fun q : (Set.Ici (0 : ℝ) ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN q.1.1.1 q.1.1.2 q.2) :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_joint_continuous
      H N hN).comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
  have hKernel : Continuous
      (fun q : (Set.Ici (0 : ℝ) ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N q.1.1.1 q.2 q.1.2) :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_joint_continuous H N).comp
      ((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).prodMk
        (continuous_snd.prodMk (continuous_snd.comp continuous_fst)))
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
  exact hVacuum.mul hKernel

/-- Pointwise positivity supplies the generic normalization theorem's weight
condition. It is distinct from positivity of the actual total mass. -/
private theorem kernelSection_continuousWeight_nonneg
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    0 ≤ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
      H N hN beta hbeta C A := by
  exact (mul_pos
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H N hN beta hbeta A)
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos H N beta A C)).le

/-- The actual positive mass is inherited by integrating the existing global
Haar-a.e. equality of weights. No estimate uniform in volume is used. -/
private theorem kernelSection_continuousWeight_integral_pos
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    0 < ∫ A,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
        H N hN beta hbeta C A
      ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  calc
    0 < ∫ A,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight
          H N hN beta hbeta C A
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight_integral_pos
        H N hN beta hbeta C
    _ = ∫ A,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
          H N hN beta hbeta C A
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) :=
      integral_congr_ae
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight_ae_eq_continuousWeight
          H N hN beta hbeta C)

/-- Joint continuity of the normalized density with its literal normalization
integral. Positivity is discharged by the existing model, not an extra input. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionNormalizedDensity_beta_joint_continuous
    (H N : ℕ) (hN : 0 < N) :
    Continuous (fun q : (Set.Ici (0 : ℝ) ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
      (∫ A,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
          H N hN q.1.1.1 q.1.1.2 q.1.2 A
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))⁻¹ *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
        H N hN q.1.1.1 q.1.1.2 q.1.2 q.2) := by
  exact realIntegralWeightedDensity_joint_continuous
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
    (fun p : Set.Ici (0 : ℝ) ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
        H N hN p.1.1 p.1.2 p.2)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight_beta_joint_continuous
      H N hN)
    (fun p => kernelSection_continuousWeight_integral_pos H N hN p.1.1 p.1.2 p.2)

/-- Expectations of jointly continuous tests under the existing fixed-right
continuous-density probability law are jointly continuous in beta and boundary. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_integral_beta_joint_continuous
    (H N : ℕ) (hN : 0 < N)
    (f : (Set.Ici (0 : ℝ) ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) →
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hf : Continuous (Function.uncurry f)) :
    Continuous (fun p : Set.Ici (0 : ℝ) ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
      ∫ A, f p A ∂
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN p.1.1 p.1.2 p.2)) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
  exact realIntegralWeightedProbabilityMeasure_integral_continuous
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
    (fun p : Set.Ici (0 : ℝ) ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
        H N hN p.1.1 p.1.2 p.2)
    f
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight_beta_joint_continuous
      H N hN)
    hf
    (fun p A => kernelSection_continuousWeight_nonneg H N hN p.1.1 p.1.2 p.2 A)
    (fun p => kernelSection_continuousWeight_integral_pos H N hN p.1.1 p.1.2 p.2)

/-- Transfer to the original L2-presented measure through the established
measure equality. No point evaluation of an L2 class occurs in this argument. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionProbabilityMeasure_integral_beta_joint_continuous
    (H N : ℕ) (hN : 0 < N)
    (f : (Set.Ici (0 : ℝ) ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) →
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hf : Continuous (Function.uncurry f)) :
    Continuous (fun p : Set.Ici (0 : ℝ) ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
      ∫ A, f p A ∂
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionProbabilityMeasure
          H N hN p.1.1 p.1.2 p.2)) := by
  have heq :
      (fun p : Set.Ici (0 : ℝ) ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        ∫ A, f p A ∂
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionProbabilityMeasure
            H N hN p.1.1 p.1.2 p.2)) =
      (fun p : Set.Ici (0 : ℝ) ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        ∫ A, f p A ∂
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN p.1.1 p.1.2 p.2)) := by
    funext p
    exact congrArg
      (fun nu : Measure (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) =>
        ∫ A, f p A ∂nu)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionProbabilityMeasure_eq_continuous
        H N hN p.1.1 p.1.2 p.2)
  exact Eq.mpr
    (congrArg (fun g : (Set.Ici (0 : ℝ) ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ => Continuous g) heq)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_integral_beta_joint_continuous
      H N hN f hf)

end

end MGAP4D.MathlibAnalytic
