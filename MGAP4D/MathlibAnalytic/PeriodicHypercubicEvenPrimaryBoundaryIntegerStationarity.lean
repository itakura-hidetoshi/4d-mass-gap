import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryTemporalTranslationCovariance
import Mathlib.Tactic

/-!
# Integer stationarity of the one-sided primary spatial Wilson readout law

The previous layer proves the pointwise finite-lattice covariance

`R_{k+m}(A) = R_m(T_{-k} A)`.

The canonical finite periodic `SU(N)` Wilson Gibbs measure is already exactly invariant under every
integer temporal configuration translation.  Combining those two same-source facts with
`Measure.map_map` gives stationarity of the actual primary spatial readout law at integer lattice
times.

This file stays entirely at one finite Wilson scale.  No rational-floor alignment, continuum
time-translation invariance, OS contraction, null-space preservation, semigroup, Hamiltonian,
spectral statement, or mass-gap transfer is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Function

noncomputable section

local instance primaryIntegerStationarityIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (SpecialUnitaryMatrixGroup N) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance primaryIntegerStationarityCompactSpace (N : ℕ) :
    CompactSpace (SpecialUnitaryMatrixGroup N) :=
  specialUnitaryGroupCompactSpace N

local instance primaryIntegerStationaritySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (SpecialUnitaryMatrixGroup N) :=
  specialUnitaryGroupSecondCountableTopology N

local instance primaryIntegerStationarityMeasurableSpace (N : ℕ) :
    MeasurableSpace (SpecialUnitaryMatrixGroup N) :=
  specialUnitaryGroupMeasurableSpace N

local instance primaryIntegerStationarityBorelSpace (N : ℕ) :
    BorelSpace (SpecialUnitaryMatrixGroup N) :=
  specialUnitaryGroupBorelSpace N

/-- The pushforward law of the one-sided primary spatial readout is stationary under every
nonnegative integer shift of its lattice-time index. -/
theorem periodicHypercubicEvenPrimarySpatialBoundaryReadoutAtTime_wilsonGibbs_law_stationary
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (m k : ℕ) :
    Measure.map
        (periodicHypercubicEvenPrimarySpatialBoundaryReadoutAtTime
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) H (k + m))
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure =
      Measure.map
        (periodicHypercubicEvenPrimarySpatialBoundaryReadoutAtTime
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) H m)
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure := by
  letI : NeZero (PeriodicHypercubicEvenSideLength H) := by
    refine ⟨?_⟩
    simp [PeriodicHypercubicEvenSideLength]
  let T :=
    periodicHypercubicIntegerTemporalConfigurationTranslation
      (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
      (PeriodicHypercubicEvenSideLength H) (-(k : ℤ))
  have hT : Measurable T :=
    (periodicHypercubicIntegerTemporalConfigurationTranslation
      (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
      (PeriodicHypercubicEvenSideLength H) (-(k : ℤ))).measurable
  have hR : Measurable
      (periodicHypercubicEvenPrimarySpatialBoundaryReadoutAtTime
        (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) H m) :=
    periodicHypercubicEvenPrimarySpatialBoundaryReadoutAtTime_measurable H m
  have hcov :
      periodicHypercubicEvenPrimarySpatialBoundaryReadoutAtTime
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) H (k + m) =
        (periodicHypercubicEvenPrimarySpatialBoundaryReadoutAtTime
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) H m) ∘ T := by
    funext A
    exact
      periodicHypercubicEvenPrimarySpatialBoundaryReadoutAtTime_add_eq_neg_configurationTranslation
        H m k A
  rw [hcov]
  calc
    Measure.map
        ((periodicHypercubicEvenPrimarySpatialBoundaryReadoutAtTime
            (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) H m) ∘ T)
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure =
      Measure.map
        (periodicHypercubicEvenPrimarySpatialBoundaryReadoutAtTime
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) H m)
        (Measure.map T
          (periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure) :=
      (Measure.map_map hR hT).symm
    _ = Measure.map
        (periodicHypercubicEvenPrimarySpatialBoundaryReadoutAtTime
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) H m)
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure := by
      exact congrArg
        (Measure.map
          (periodicHypercubicEvenPrimarySpatialBoundaryReadoutAtTime
            (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) H m))
        (periodicHypercubicSpecialUnitary_gibbs_map_integerTemporalTranslation_eq_self
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta (-(k : ℤ)))

/-- In particular, every nonnegative integer-time primary readout has exactly the same Wilson law
as the primary fixed-slice readout at time zero. -/
theorem periodicHypercubicEvenPrimarySpatialBoundaryReadoutAtTime_wilsonGibbs_law_eq_zero
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (k : ℕ) :
    Measure.map
        (periodicHypercubicEvenPrimarySpatialBoundaryReadoutAtTime
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) H k)
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure =
      Measure.map
        (periodicHypercubicEvenPrimarySpatialBoundaryReadoutAtTime
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) H 0)
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure := by
  simpa using
    (periodicHypercubicEvenPrimarySpatialBoundaryReadoutAtTime_wilsonGibbs_law_stationary
      H N hN beta hbeta 0 k)

end

end MathlibAnalytic
end MGAP4D
