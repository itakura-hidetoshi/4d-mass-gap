import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRealizableDiscreteSemigroup
import Mathlib.Tactic

noncomputable section

open MeasureTheory

namespace MGAP4D
namespace MathlibAnalytic

local instance realizableOneStepDerivedRateGapSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance realizableOneStepDerivedRateGapSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance realizableOneStepDerivedRateGapSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance realizableOneStepDerivedRateGapSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance realizableOneStepDerivedRateGapSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance realizableOneStepDerivedRateGapSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

namespace PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta}
    {E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S}

/-- Actual finite-state stationarity preserves the OS state coefficient under
any realizable nonnegative integer temporal displacement.

This theorem is independent of any proposed mass value. -/
theorem realizableCarrierTranslation_omega_stationary
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n k : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    Pn.omega
        (R.realizableCarrierTranslation hInvariant n k F).toGaugeInvariant =
      Pn.omega F.toGaugeInvariant := by
  dsimp only
  change
    physicalYangMillsApproximatingGaugeInvariantWeakStarState S n
        (R.fullTranslation n k F.toGaugeInvariant) =
      physicalYangMillsApproximatingGaugeInvariantWeakStarState S n
        F.toGaugeInvariant
  exact R.approximatingState_fullTranslation_invariant n k F.toGaugeInvariant

/-- Vacuum centering commutes with the actual integer-time carrier translation,
using only finite-state stationarity and preservation of the unit. -/
theorem realizableCarrierTranslation_vacuumCenteredCarrier_stationary
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n k : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    R.realizableCarrierTranslation hInvariant n k (Pn.vacuumCenteredCarrier F) =
      Pn.vacuumCenteredCarrier
        (R.realizableCarrierTranslation hInvariant n k F) := by
  dsimp only
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  unfold PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.vacuumCenteredCarrier
  rw [map_sub, map_smul,
    R.realizableCarrierTranslation_vacuumObservable hInvariant n k]
  rw [R.realizableCarrierTranslation_omega_stationary hInvariant n k F]

end PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance

/-- A realizable one-lattice-step centered OS estimate with an arbitrary
scale-dependent factor `rₙ`.

No continuum mass and no exact numerical value occur in this finite package.
The only quantitative statement is the actual one-step bound. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepGapCertificate
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S)
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (transferFactor : ℕ → ℝ) where
  transferFactor_nonneg : ∀ n, 0 ≤ transferFactor n
  oneStep_centered_norm_le :
    ∀ (n : ℕ)
      (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier),
      let Pn :=
        physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
      ‖R.realizableCarrierTranslation hInvariant n 1
          (Pn.vacuumCenteredCarrier F)‖ ≤
        transferFactor n * ‖Pn.vacuumCenteredCarrier F‖

namespace PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepGapCertificate

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta}
    {E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S}
    {R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    {transferFactor : ℕ → ℝ}

/-- The one-step finite Wilson estimate generates the geometric norm bound at
all genuine integer lattice times. -/
theorem centered_norm_le_pow
    (G : PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant transferFactor)
    (n k : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    ‖R.realizableCarrierTranslation hInvariant n k
        (Pn.vacuumCenteredCarrier F)‖ ≤
      (transferFactor n) ^ k * ‖Pn.vacuumCenteredCarrier F‖ := by
  dsimp only
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  let r := transferFactor n
  induction k with
  | zero =>
      rw [R.realizableCarrierTranslation_zero]
      simp
  | succ k ih =>
      have hcomm :=
        R.realizableCarrierTranslation_vacuumCenteredCarrier_stationary
          hInvariant n k F
      have hstep :=
        G.oneStep_centered_norm_le n
          (R.realizableCarrierTranslation hInvariant n k F)
      dsimp only at hstep
      change
        ‖R.realizableCarrierTranslation hInvariant n (k + 1)
            (Pn.vacuumCenteredCarrier F)‖ ≤
          r ^ (k + 1) * ‖Pn.vacuumCenteredCarrier F‖
      calc
        ‖R.realizableCarrierTranslation hInvariant n (k + 1)
            (Pn.vacuumCenteredCarrier F)‖ =
          ‖R.realizableCarrierTranslation hInvariant n 1
              (R.realizableCarrierTranslation hInvariant n k
                (Pn.vacuumCenteredCarrier F))‖ := by
            rw [R.realizableCarrierTranslation_add]
        _ = ‖R.realizableCarrierTranslation hInvariant n 1
              (Pn.vacuumCenteredCarrier
                (R.realizableCarrierTranslation hInvariant n k F))‖ := by
            rw [hcomm]
        _ ≤ r *
              ‖Pn.vacuumCenteredCarrier
                (R.realizableCarrierTranslation hInvariant n k F)‖ := hstep
        _ = r *
              ‖R.realizableCarrierTranslation hInvariant n k
                (Pn.vacuumCenteredCarrier F)‖ := by
            rw [← hcomm]
        _ ≤ r * (r ^ k * ‖Pn.vacuumCenteredCarrier F‖) := by
            exact mul_le_mul_of_nonneg_left ih (G.transferFactor_nonneg n)
        _ = r ^ (k + 1) * ‖Pn.vacuumCenteredCarrier F‖ := by
            rw [pow_succ]
            ring

/-- Squaring the generated norm estimate gives the discrete centered OS
quadratic decay with the same actual finite factor. -/
theorem centered_osQuadraticValue_le_pow_sq
    (G : PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant transferFactor)
    (n k : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    Pn.osQuadraticValue
        (R.realizableCarrierTranslation hInvariant n k
          (Pn.vacuumCenteredCarrier F)) ≤
      ((transferFactor n) ^ k) ^ 2 *
        Pn.osQuadraticValue (Pn.vacuumCenteredCarrier F) := by
  dsimp only
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  have hnorm := G.centered_norm_le_pow n k F
  dsimp only at hnorm
  rw [Pn.osQuadraticValue_eq_norm_sq, Pn.osQuadraticValue_eq_norm_sq]
  have hfactor : 0 ≤ (transferFactor n) ^ k :=
    pow_nonneg (G.transferFactor_nonneg n) k
  nlinarith [norm_nonneg
    (R.realizableCarrierTranslation hInvariant n k
      (Pn.vacuumCenteredCarrier F)),
    norm_nonneg (Pn.vacuumCenteredCarrier F)]

end PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepGapCertificate

end MathlibAnalytic
end MGAP4D

end