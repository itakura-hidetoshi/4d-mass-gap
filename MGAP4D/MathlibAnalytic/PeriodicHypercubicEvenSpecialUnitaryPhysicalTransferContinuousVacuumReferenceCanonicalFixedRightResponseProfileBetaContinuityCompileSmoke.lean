import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceFixedRightTargetRatioResponseBetaContinuity
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCanonicalFixedRightCoefficientContinuityLift

/-! Regression contracts for the original canonical profile and coefficient.
The initial test-first commit deliberately requires the missing new endpoints.
All ordered pairs, the zero endpoint, original weights, and cutoff are retained. -/

namespace MGAP4D.MathlibAnalytic

noncomputable section

set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 50000

local instance canonicalProfileBetaContinuitySmokeSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance canonicalProfileBetaContinuitySmokeSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance canonicalProfileBetaContinuitySmokeSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance canonicalProfileBetaContinuitySmokeSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance canonicalProfileBetaContinuitySmokeSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance canonicalProfileBetaContinuitySmokeSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

-- Existential witnesses and the compact product image have the SAME order.
example (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseValueSet
        H N hN beta hbeta target source =
      (fun p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          ((Matrix.specialUnitaryGroup (Fin N) ℂ × Matrix.specialUnitaryGroup (Fin N) ℂ) ×
            (Matrix.specialUnitaryGroup (Fin N) ℂ × Matrix.specialUnitaryGroup (Fin N) ℂ)) =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs
          H N hN beta hbeta p.1 target source p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2) ''
        Set.univ := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseValueSet_eq_image_univ
      H N hN beta hbeta target source

-- No continuity hypothesis on R_can is supplied.
example (H N : ℕ) (hN : 0 < N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    Continuous (fun beta : Set.Ici (0 : ℝ) =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
        H N hN beta.1 beta.2 target source) := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_continuous
      H N hN target source

-- Simultaneously retain beta = 0 and target = source.
example (H N : ℕ) (hN : 0 < N) (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    ContinuousAt (fun beta : Set.Ici (0 : ℝ) =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
        H N hN beta.1 beta.2 e e)
      ⟨0, by change (0 : ℝ) ≤ 0; exact le_rfl⟩ := by
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_continuous
      H N hN e e).continuousAt

-- An arbitrary parameter space may traverse the original profile.
example {P : Type*} [TopologicalSpace P] (H N : ℕ) (hN : 0 < N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (beta : P → Set.Ici (0 : ℝ)) (hbeta : Continuous beta) :
    Continuous (fun p =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
        H N hN (beta p).1 (beta p).2 target source) := by
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_continuous
      H N hN target source).comp hbeta

-- Use the EXISTING zero-filled path, rather than introducing a proxy.
example (H N : ℕ) (hN : 0 < N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    ContinuousOn
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfilePath
        H N hN target source) (Set.Ici 0) := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfilePath_continuousOn_Ici
      H N hN target source

-- The exact weighted coefficient path, with the original weight condition.
example (H N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 1 ≤ s)
    (center : PeriodicHypercubicEvenSpatialSliceLink H) :
    ContinuousOn
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficientPath
        H N hN s center) (Set.Ici 0) := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficientPath_continuousOn_Ici
      H N hN s hs center

-- The same continuity is exposed directly for the original coefficient.
example (H N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 1 ≤ s)
    (center : PeriodicHypercubicEvenSpatialSliceLink H) :
    Continuous (fun beta : Set.Ici (0 : ℝ) =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient
        H N hN beta.1 beta.2 s center) := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient_continuous
      H N hN s hs center

-- No response/coefficient continuity premise remains; zero is allowed.
example (H N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 1 ≤ s)
    (center : PeriodicHypercubicEvenSpatialSliceLink H)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut : beta ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff s) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient
        H N hN beta hbeta s center <
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureBarrier := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient_lt_halfBarrier_of_nonneg_le_cutoff
      H N hN s hs center beta hbeta hcut

end

end MGAP4D.MathlibAnalytic
