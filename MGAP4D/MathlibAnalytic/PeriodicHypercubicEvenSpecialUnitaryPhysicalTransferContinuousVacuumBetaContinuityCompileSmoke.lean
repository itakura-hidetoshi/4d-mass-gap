import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumBetaContinuity

namespace MGAP4D.MathlibAnalytic

noncomputable section

-- The compact-open bridge must not require first countability or a metric on P.
example {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    (k : P → C(X, ℝ))
    (h : Continuous (fun q : P × X => k q.1 q.2)) : Continuous k :=
  (ContinuousMap.curry ⟨_, h⟩).continuous

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

-- No separately chosen pointwise representative or regularity input is accepted.
example (H N : ℕ) (hN : 0 < N) :
    Continuous
      (fun p : Set.Ici (0 : ℝ) ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN p.1.1 p.1.2 p.2) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_joint_continuous
    H N hN

-- The codomain is the existing compact boundary's continuous-function space,
-- with its sup norm, not merely the pointwise function topology.
example (H N : ℕ) (hN : 0 < N) :
    Continuous
      (fun beta : Set.Ici (0 : ℝ) =>
        (⟨periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H N hN beta.1 beta.2,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_continuous
            H N hN beta.1 beta.2⟩ :
          C(PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N, ℝ))) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_supNorm_continuous
    H N hN

-- Positivity must discharge the reciprocal denominator on the actual model.
example (H N : ℕ) (hN : 0 < N) :
    Continuous
      (fun p : Set.Ici (0 : ℝ) ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN p.1.1 p.1.2 p.2)⁻¹) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_inv_joint_continuous
    H N hN

-- The raw-kernel endpoint is valid on all real couplings.
example (H N : ℕ) :
    Continuous
      (fun p : ℝ ×
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N p.1 p.2.1 p.2.2) :=
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_joint_continuous H N

-- The vacuum endpoint includes beta = 0, in the half-line's subspace topology.
example (H N : ℕ) (hN : 0 < N)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    ContinuousAt
      (fun p : Set.Ici (0 : ℝ) ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN p.1.1 p.1.2 p.2)
      (⟨0, le_rfl⟩, A) :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_joint_continuous
    H N hN).continuousAt

end

end MGAP4D.MathlibAnalytic
