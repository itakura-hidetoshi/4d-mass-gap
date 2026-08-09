import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRealizableDiscreteSemigroup
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSExact3320FiniteIntegralActualBoundaryGap
import Mathlib.Tactic

noncomputable section

open MeasureTheory

namespace MGAP4D
namespace MathlibAnalytic

local instance realizableOneStepExact3320GapSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance realizableOneStepExact3320GapSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance realizableOneStepExact3320GapSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance realizableOneStepExact3320GapSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance realizableOneStepExact3320GapSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance realizableOneStepExact3320GapSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Exact one-lattice-step norm factor at scale `n`. -/
def physicalYangMillsExact3320OneStepNormFactor
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit) (n : ℕ) : ℝ :=
  Real.exp (-physicalYangMillsExact3320Mass * S.latticeSpacing n)

/-- The exact one-step factor is positive. -/
theorem physicalYangMillsExact3320OneStepNormFactor_pos
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit) (n : ℕ) :
    0 < physicalYangMillsExact3320OneStepNormFactor S n := by
  exact Real.exp_pos _

/-- The exact one-step factor is at most one because both the normalized mass
and the physical lattice spacing are positive. -/
theorem physicalYangMillsExact3320OneStepNormFactor_le_one
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit) (n : ℕ) :
    physicalYangMillsExact3320OneStepNormFactor S n ≤ 1 := by
  unfold physicalYangMillsExact3320OneStepNormFactor
  rw [Real.exp_le_one_iff]
  exact neg_nonpos.mpr
    (mul_nonneg physicalYangMillsExact3320Mass_pos.le
      (S.latticeSpacing_pos n).le)

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

/-- Realizable carrier translation preserves the finite approximating state
coefficient. -/
theorem realizableCarrierTranslation_omega
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

/-- Vacuum centering commutes with every realizable discrete carrier
translation. -/
theorem realizableCarrierTranslation_vacuumCenteredCarrier
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
  rw [R.realizableCarrierTranslation_omega hInvariant n k F]

/-- The carrier action at `k` realizable lattice steps is the `k`-fold iterate
of the actual one-step carrier action. -/
theorem realizableCarrierTranslation_eq_iterate_one
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n k : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    R.realizableCarrierTranslation hInvariant n k F =
      (fun G => R.realizableCarrierTranslation hInvariant n 1 G)^[k] F := by
  induction k with
  | zero =>
      rw [R.realizableCarrierTranslation_zero]
      rfl
  | succ k ih =>
      rw [R.realizableCarrierTranslation_add, ih,
        Function.iterate_succ_apply']

end PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance

/-- Remaining quantitative finite-lattice input after realizable temporal
stationarity, reflection exchange, and discrete semigroup algebra have been
constructed.

Only the centered one-lattice-step OS norm estimate is retained, with its factor
fixed to the exact normalized mass `33/20`. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320GapCertificate
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
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)) where
  oneStep_centered_norm_le :
    ∀ (n : ℕ)
      (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier),
      let Pn :=
        physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
      ‖R.realizableCarrierTranslation hInvariant n 1
          (Pn.vacuumCenteredCarrier F)‖ ≤
        physicalYangMillsExact3320OneStepNormFactor S n *
          ‖Pn.vacuumCenteredCarrier F‖

namespace PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320GapCertificate

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

/-- The single strict one-step estimate generates the exact geometric norm
bound at every realizable nonnegative lattice step count. -/
theorem centered_norm_le_pow
    (G : PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320GapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n k : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    ‖R.realizableCarrierTranslation hInvariant n k
        (Pn.vacuumCenteredCarrier F)‖ ≤
      (physicalYangMillsExact3320OneStepNormFactor S n) ^ k *
        ‖Pn.vacuumCenteredCarrier F‖ := by
  dsimp only
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  let r := physicalYangMillsExact3320OneStepNormFactor S n
  induction k with
  | zero =>
      rw [R.realizableCarrierTranslation_zero]
      simp
  | succ k ih =>
      have hcomm :=
        R.realizableCarrierTranslation_vacuumCenteredCarrier
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
            exact mul_le_mul_of_nonneg_left ih
              (physicalYangMillsExact3320OneStepNormFactor_pos S n).le
        _ = r ^ (k + 1) * ‖Pn.vacuumCenteredCarrier F‖ := by
            rw [pow_succ]
            ring

/-- Squaring the generated norm estimate gives the corresponding discrete OS
quadratic decay. -/
theorem centered_osQuadraticValue_le_pow_sq
    (G : PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320GapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n k : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    Pn.osQuadraticValue
        (R.realizableCarrierTranslation hInvariant n k
          (Pn.vacuumCenteredCarrier F)) ≤
      ((physicalYangMillsExact3320OneStepNormFactor S n) ^ k) ^ 2 *
        Pn.osQuadraticValue (Pn.vacuumCenteredCarrier F) := by
  dsimp only
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  have hnorm := G.centered_norm_le_pow n k F
  dsimp only at hnorm
  rw [Pn.osQuadraticValue_eq_norm_sq, Pn.osQuadraticValue_eq_norm_sq]
  have hfactor :
      0 ≤ (physicalYangMillsExact3320OneStepNormFactor S n) ^ k := by
    positivity
  nlinarith [norm_nonneg
    (R.realizableCarrierTranslation hInvariant n k
      (Pn.vacuumCenteredCarrier F)),
    norm_nonneg (Pn.vacuumCenteredCarrier F)]

/-- The discrete OS quadratic estimate is exactly the corresponding actual
finite periodic Wilson reflected-integral estimate. -/
theorem centered_finiteReflectedIntegral_le_pow_sq
    (G : PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320GapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n k : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
        (R.realizableCarrierTranslation hInvariant n k
          ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
            S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).vacuumCenteredCarrier F)) ≤
      ((physicalYangMillsExact3320OneStepNormFactor S n) ^ k) ^ 2 *
        physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
          ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
            S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).vacuumCenteredCarrier F) := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  rw [← physical_yang_mills_evenPeriodicWilsonOS_osQuadraticValue_eq_finiteReflectedIntegral,
    ← physical_yang_mills_evenPeriodicWilsonOS_osQuadraticValue_eq_finiteReflectedIntegral]
  exact G.centered_osQuadraticValue_le_pow_sq n k F

end PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320GapCertificate

end MathlibAnalytic
end MGAP4D

end
