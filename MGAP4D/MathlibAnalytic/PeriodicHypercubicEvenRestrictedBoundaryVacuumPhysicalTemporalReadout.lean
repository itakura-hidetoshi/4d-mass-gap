import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryVacuumMomentRestrictionGaugeTransport
import MGAP4D.MathlibAnalytic.PeriodicHypercubicIntegerTemporalTranslation

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance restrictedBoundaryVacuumTemporalReadoutNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance restrictedBoundaryVacuumTemporalReadoutTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance restrictedBoundaryVacuumTemporalReadoutCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance restrictedBoundaryVacuumTemporalReadoutSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance restrictedBoundaryVacuumTemporalReadoutMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance restrictedBoundaryVacuumTemporalReadoutBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The boundary-vacuum scalar readout at integer Euclidean time `t`.

The time-`t` slice is defined by transporting the configuration back by `t`
lattice units and then evaluating the already constructed reflection-fixed
boundary readout.  This convention makes temporal covariance literal:
`Ψ^(t+k) (T_k A) = Ψ^t A`.

No physical time-translation action on `ℝ` is postulated here. -/
noncomputable def periodicHypercubicEvenRestrictedBoundaryVacuumMomentAtTime
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (t : ℤ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  periodicHypercubicEvenRestrictedBoundaryVacuumMoment
    H N hN beta hbeta
    (periodicHypercubicIntegerTemporalConfigurationTranslation
      (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
      (PeriodicHypercubicEvenSideLength H) (-t) A)

/-- The time-indexed family extends the original reflection-fixed readout at
integer time zero. -/
@[simp]
theorem periodicHypercubicEvenRestrictedBoundaryVacuumMomentAtTime_zero
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenRestrictedBoundaryVacuumMomentAtTime
        H N hN beta hbeta 0 A =
      periodicHypercubicEvenRestrictedBoundaryVacuumMoment
        H N hN beta hbeta A := by
  simp [periodicHypercubicEvenRestrictedBoundaryVacuumMomentAtTime]

/-- Exact finite temporal covariance of the time-indexed boundary-vacuum
readout.

This is generated solely from the additive action law of the actual periodic
integer temporal translations.  In particular, it does not identify temporal
translation with the identity on the scalar carrier. -/
theorem periodicHypercubicEvenRestrictedBoundaryVacuumMomentAtTime_integerTemporal_covariant
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (t k : ℤ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenRestrictedBoundaryVacuumMomentAtTime
        H N hN beta hbeta (t + k)
        (periodicHypercubicIntegerTemporalConfigurationTranslation
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
          (PeriodicHypercubicEvenSideLength H) k A) =
      periodicHypercubicEvenRestrictedBoundaryVacuumMomentAtTime
        H N hN beta hbeta t A := by
  have hindex : -(t + k) + k = -t := by omega
  have htranslate :
      periodicHypercubicIntegerTemporalConfigurationTranslation
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
          (PeriodicHypercubicEvenSideLength H) (-(t + k))
          (periodicHypercubicIntegerTemporalConfigurationTranslation
            (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
            (PeriodicHypercubicEvenSideLength H) k A) =
        periodicHypercubicIntegerTemporalConfigurationTranslation
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
          (PeriodicHypercubicEvenSideLength H) (-t) A := by
    rw [← periodicHypercubicIntegerTemporalConfigurationTranslation_add_apply]
    rw [hindex]
  unfold periodicHypercubicEvenRestrictedBoundaryVacuumMomentAtTime
  rw [htranslate]

/-- Scale-wise time-indexed interpolation generated from the same concrete
boundary-vacuum readout.  At `t = 0` this is exactly the existing scalar
interpolation formula; away from zero it records the translated boundary slice
rather than forcing a translation action on `ℝ`. -/
noncomputable def
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalInterpolateAtTime
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (n : ℕ) (t : ℤ)
    (A : PeriodicHypercubicEvenEdge (H n) →
      Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  periodicHypercubicEvenRestrictedBoundaryVacuumMomentAtTime
    (H n) N hN (beta n) (hbeta n) t A

@[simp]
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalInterpolateAtTime_zero
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (n : ℕ)
    (A : PeriodicHypercubicEvenEdge (H n) →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalInterpolateAtTime
        H N hN beta hbeta n 0 A =
      periodicHypercubicEvenRestrictedBoundaryVacuumMoment
        (H n) N hN (beta n) (hbeta n) A := by
  exact
    periodicHypercubicEvenRestrictedBoundaryVacuumMomentAtTime_zero
      (H n) N hN (beta n) (hbeta n) A

/-- Exact scale-wise covariance of the temporal readout family under the actual
integer lattice translation. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalInterpolateAtTime_integerTemporal_covariant
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (n : ℕ) (t k : ℤ)
    (A : PeriodicHypercubicEvenEdge (H n) →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalInterpolateAtTime
        H N hN beta hbeta n (t + k)
        (periodicHypercubicIntegerTemporalConfigurationTranslation
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
          (PeriodicHypercubicEvenSideLength (H n)) k A) =
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalInterpolateAtTime
        H N hN beta hbeta n t A := by
  exact
    periodicHypercubicEvenRestrictedBoundaryVacuumMomentAtTime_integerTemporal_covariant
      (H n) N hN (beta n) (hbeta n) t k A

end

end MathlibAnalytic
end MGAP4D
