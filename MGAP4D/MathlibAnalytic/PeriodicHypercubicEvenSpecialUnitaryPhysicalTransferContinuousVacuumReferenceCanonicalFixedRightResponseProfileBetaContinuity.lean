import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceFixedRightTargetRatioResponseBetaContinuity
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCanonicalFixedRightCoefficientContinuityLift
import Mathlib.Topology.Order.Compact

/-!
# Continuity of the original canonical fixed-right response profile

The literal response is jointly continuous on nonnegative coupling times the
fixed compact configuration/four-group-value space. Identify the ORIGINAL
existential value set with its image, take the compact supremum using the pinned
mathlib theorem, and return to the unchanged max-with-zero definition.

This discharges the analytic input of the existing finite weighted-column
continuity lift and half-barrier continuation theorem. The resulting strict
bound is for the original coefficient, with the original scale condition and
cutoff. Zero coupling and coincident target/source are included.

No response, coefficient, law, vacuum, or cutoff is redefined. No continuity
hypothesis, positive-beta restriction, or volume-dependent cutoff is added.
-/

namespace MGAP4D.MathlibAnalytic

noncomputable section

set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 50000

/-- Take the compact supremum before specializing to the concrete Wilson
construction, so elaboration never needs to unfold that construction here. -/
private theorem canonicalProfileBetaContinuity_continuous_max_sSup
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X] [CompactSpace X]
    (D : P → X → ℝ) (hD : Continuous (Function.uncurry D)) :
    Continuous (fun p => max 0 (sSup (D p '' (Set.univ : Set X)))) := by
  have hSup : Continuous (fun p => sSup (D p '' (Set.univ : Set X))) :=
    isCompact_univ.continuous_sSup hD
  exact continuous_max.comp (continuous_const.prodMk hSup)

local instance canonicalProfileBetaContinuitySpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance canonicalProfileBetaContinuitySpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance canonicalProfileBetaContinuitySpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance canonicalProfileBetaContinuitySpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance canonicalProfileBetaContinuitySpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance canonicalProfileBetaContinuitySpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

/-- Exact identification of the original existential value set. The target,
source, and four group witnesses retain their original order. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseValueSet_eq_image_univ
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseValueSet
        H N hN beta hbeta target source =
      (fun p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          ((Matrix.specialUnitaryGroup (Fin N) ℂ × Matrix.specialUnitaryGroup (Fin N) ℂ) ×
            (Matrix.specialUnitaryGroup (Fin N) ℂ × Matrix.specialUnitaryGroup (Fin N) ℂ)) =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs
          H N hN beta hbeta p.1 target source p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2) ''
        Set.univ := by
  apply Set.ext
  intro x
  constructor
  · rintro ⟨B, g₁, g₂, h, k, hx⟩
    exact ⟨(B, ((g₁, g₂), (h, k))), Set.mem_univ _, hx.symm⟩
  · rintro ⟨p, _hp, hx⟩
    exact ⟨p.1, p.2.1.1, p.2.1.2, p.2.2.1, p.2.2.2, hx.symm⟩

/-- Coordinatewise beta continuity of the ORIGINAL max-with-zero supremum
profile, on the closed nonnegative half-line and for every ordered link pair. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_continuous
    (H N : ℕ) (hN : 0 < N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    Continuous (fun beta : Set.Ici (0 : ℝ) =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
        H N hN beta.1 beta.2 target source) := by
  let Theta := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
    ((Matrix.specialUnitaryGroup (Fin N) ℂ × Matrix.specialUnitaryGroup (Fin N) ℂ) ×
      (Matrix.specialUnitaryGroup (Fin N) ℂ × Matrix.specialUnitaryGroup (Fin N) ℂ))
  let D : Set.Ici (0 : ℝ) → Theta → ℝ := fun beta p =>
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs
      H N hN beta.1 beta.2 p.1 target source p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2
  have hD : Continuous (Function.uncurry D) :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs_joint_continuous
      H N hN target source
  have hMax : Continuous (fun beta => max 0 (sSup (D beta '' (Set.univ : Set Theta)))) :=
    canonicalProfileBetaContinuity_continuous_max_sSup D hD
  have heq :
      (fun beta : Set.Ici (0 : ℝ) =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
          H N hN beta.1 beta.2 target source) =
      (fun beta => max 0 (sSup (D beta '' (Set.univ : Set Theta)))) := by
    funext beta
    have hValues :
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseValueSet
            H N hN beta.1 beta.2 target source =
          D beta '' (Set.univ : Set Theta) :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseValueSet_eq_image_univ
        H N hN beta.1 beta.2 target source
    exact congrArg (fun S : Set ℝ => max (0 : ℝ) (sSup S)) hValues
  exact Eq.mpr (congrArg (fun f : Set.Ici (0 : ℝ) → ℝ => Continuous f) heq) hMax

/-- Continuity on the half-line of the EXISTING zero-filled response path.
This statement makes no assertion about its negative-coupling extension. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfilePath_continuousOn_Ici
    (H N : ℕ) (hN : 0 < N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    ContinuousOn
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfilePath
        H N hN target source) (Set.Ici 0) := by
  apply continuousOn_iff_continuous_restrict.mpr
  have heq :
      (fun beta : Set.Ici (0 : ℝ) =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfilePath
          H N hN target source beta.1) =
      (fun beta : Set.Ici (0 : ℝ) =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
          H N hN beta.1 beta.2 target source) := by
    funext beta
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfilePath_eq
        H N hN target source beta.1 beta.2
  exact Eq.mpr (congrArg (fun f : Set.Ici (0 : ℝ) → ℝ => Continuous f) heq)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_continuous
      H N hN target source)

/-- Discharge the existing coordinate-to-coefficient continuity lift for the
actual finite-volume coefficient path, retaining the original weight scale. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficientPath_continuousOn_Ici
    (H N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 1 ≤ s)
    (center : PeriodicHypercubicEvenSpatialSliceLink H) :
    ContinuousOn
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficientPath
        H N hN s center) (Set.Ici 0) := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficientPath_continuousOn_of_responseProfilePath
      H N hN s hs center (Set.Ici 0)
      (fun target source =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfilePath_continuousOn_Ici
          H N hN target source)

/-- The same continuity stated directly for the ORIGINAL exact weighted
coefficient, rather than for its auxiliary total real path. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient_continuous
    (H N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 1 ≤ s)
    (center : PeriodicHypercubicEvenSpatialSliceLink H) :
    Continuous (fun beta : Set.Ici (0 : ℝ) =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient
        H N hN beta.1 beta.2 s center) := by
  have hPath : Continuous (fun beta : Set.Ici (0 : ℝ) =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficientPath
        H N hN s center beta.1) :=
    continuousOn_iff_continuous_restrict.mp
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficientPath_continuousOn_Ici
        H N hN s hs center)
  have heq :
      (fun beta : Set.Ici (0 : ℝ) =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficientPath
          H N hN s center beta.1) =
      (fun beta : Set.Ici (0 : ℝ) =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient
          H N hN beta.1 beta.2 s center) := by
    funext beta
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficientPath_eq
        H N hN s center beta.1 beta.2
  exact Eq.mp (congrArg (fun f : Set.Ici (0 : ℝ) → ℝ => Continuous f) heq) hPath

/-- Actual half-barrier discharge: no response or coefficient continuity
premise remains. The original cutoff and s >= 1 are retained, including beta=0. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient_lt_halfBarrier_of_nonneg_le_cutoff
    (H N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 1 ≤ s)
    (center : PeriodicHypercubicEvenSpatialSliceLink H)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut : beta ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff s) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient
        H N hN beta hbeta s center <
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureBarrier := by
  have hContinuous :
      ContinuousOn
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficientPath
          H N hN s center)
        (Set.Icc 0
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff s)) :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficientPath_continuousOn_Ici
      H N hN s hs center).mono (fun _ hx => hx.1)
  have hPathLt :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficientPath_lt_halfBarrier_of_continuousOn
      H N hN s hs center hContinuous beta ⟨hbeta, hcut⟩
  have hPathEq :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficientPath_eq
      H N hN s center beta hbeta
  exact Eq.mp (congrArg (fun x : ℝ =>
    x < periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureBarrier)
    hPathEq) hPathLt

end

end MGAP4D.MathlibAnalytic
