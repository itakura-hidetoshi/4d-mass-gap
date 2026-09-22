import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumGroundStateKernelSectionBetaContinuity
import MGAP4D.MathlibAnalytic.RealIntegralWeightedProbabilityContinuity

namespace MGAP4D.MathlibAnalytic

open MeasureTheory

noncomputable section

local instance (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

-- No new vacuum choice or regularity input is supplied.
example (H N : ℕ) (hN : 0 < N) :
    Continuous (fun q : (Set.Ici (0 : ℝ) ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
        H N hN q.1.1.1 q.1.1.2 q.1.2 q.2) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight_beta_joint_continuous
    H N hN

-- The actual normalization integral remains in the conclusion.
example (H N : ℕ) (hN : 0 < N) :
    Continuous (fun q : (Set.Ici (0 : ℝ) ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
      (∫ A,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
          H N hN q.1.1.1 q.1.1.2 q.1.2 A
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))⁻¹ *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
        H N hN q.1.1.1 q.1.1.2 q.1.2 q.2) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionNormalizedDensity_beta_joint_continuous
    H N hN

-- A jointly varying observable is integrated under the existing continuous-density law.
example (H N : ℕ) (hN : 0 < N)
    (f : (Set.Ici (0 : ℝ) ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) →
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hf : Continuous (Function.uncurry f)) :
    Continuous (fun p : Set.Ici (0 : ℝ) ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
      ∫ A, f p A ∂
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN p.1.1 p.1.2 p.2)) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_integral_beta_joint_continuous
    H N hN f hf

-- The original L2-presented law is literally the conclusion; no measure replacement hypothesis.
example (H N : ℕ) (hN : 0 < N)
    (f : (Set.Ici (0 : ℝ) ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) →
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hf : Continuous (Function.uncurry f)) :
    Continuous (fun p : Set.Ici (0 : ℝ) ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
      ∫ A, f p A ∂
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionProbabilityMeasure
          H N hN p.1.1 p.1.2 p.2)) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionProbabilityMeasure_integral_beta_joint_continuous
    H N hN f hf

end

end MGAP4D.MathlibAnalytic
