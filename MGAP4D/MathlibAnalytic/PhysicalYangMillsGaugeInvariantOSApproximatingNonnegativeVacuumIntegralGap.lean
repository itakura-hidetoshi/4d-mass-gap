import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingFiniteIntegralGap
import Mathlib.Tactic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

/-- A completed finite-volume Wilson OS vacuum-gap certificate whose norm-decay
factor is explicitly nonnegative.

The existing forward finite-integral route automatically produces such a
factor because it is a square root.  Recording nonnegativity in the reverse
direction is exactly what is needed to recover the quadratic factor without
replacing the decay rate by an absolute value. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSApproximatingNonnegativeVacuumGapCertificate
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant)
    extends PhysicalYangMillsEvenPeriodicWilsonOSApproximatingVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C where
  decayFactor_nonneg : ∀ t, 0 ≤ decayFactor t

namespace PhysicalYangMillsEvenPeriodicWilsonOSApproximatingNonnegativeVacuumGapCertificate

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    {C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant}

/-- The quadratic factor canonically associated with a norm-decay factor:
translation by half the requested Euclidean time is squared. -/
def quadraticDecayFactor
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingNonnegativeVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (t : NNReal) : ℝ :=
  Q.decayFactor (t / 2) ^ 2

@[simp] theorem quadraticDecayFactor_nonneg
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingNonnegativeVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (t : NNReal) :
    0 ≤ Q.quadraticDecayFactor t := by
  exact sq_nonneg _

/-- At doubled time, the square root of the canonical quadratic factor is
exactly the original nonnegative norm-decay factor. -/
@[simp] theorem sqrt_quadraticDecayFactor_add_self
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingNonnegativeVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (t : NNReal) :
    Real.sqrt (Q.quadraticDecayFactor (t + t)) = Q.decayFactor t := by
  have hhalf : (t + t) / 2 = t := by
    ext
    norm_num <;> ring
  rw [quadraticDecayFactor, hhalf, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (Q.decayFactor_nonneg t)]

/-- Vacuum centering of any represented finite Wilson observable is orthogonal
to the normalized OS vacuum. -/
theorem physicalState_vacuumCenteredCarrier_inner_vacuum_eq_zero
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingNonnegativeVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n
    inner ℝ (Pn.physicalState (Pn.vacuumCenteredCarrier F)) Pn.vacuum = 0 := by
  dsimp only
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n
  have hPn : Pn.IsNormalized :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData_isNormalized
      S D halfExtent N hN beta hbeta B hInvariant n
  rw [Pn.physicalState_vacuumCenteredCarrier]
  unfold finiteVacuumCentered
  rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
    Pn.norm_vacuum hPn]
  simp only [one_pow, mul_one]
  exact sub_eq_zero.mpr (real_inner_comm _ _)

/-- Completed vacuum-sector norm decay recovers the half-time OS quadratic
estimate with factor `d(t / 2)^2`. -/
noncomputable def toApproximatingHalfQuadraticGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingNonnegativeVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHalfQuadraticGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C where
  mass := Q.mass
  mass_pos := Q.mass_pos
  quadraticDecayFactor := Q.quadraticDecayFactor
  quadraticDecayFactor_nonneg := Q.quadraticDecayFactor_nonneg
  slope_tendsto := by
    simpa only [Q.sqrt_quadraticDecayFactor_add_self] using Q.slope_tendsto
  exchange := Q.exchange
  finite_half_quadratic_decay := by
    intro n t
    dsimp only
    intro F
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n
    let Tn := C.toPositiveTimeObservableContractionSemigroup n
    let Fc : Pn.Carrier := Pn.vacuumCenteredCarrier F
    have horth : inner ℝ (Pn.physicalState Fc) Pn.vacuum = 0 := by
      exact Q.physicalState_vacuumCenteredCarrier_inner_vacuum_eq_zero n F
    have hdecay :
        ‖C.finiteOperator n (t / 2) (Pn.physicalState Fc)‖ ≤
          Q.decayFactor (t / 2) * ‖Pn.physicalState Fc‖ :=
      Q.finite_decay n (t / 2) (Pn.physicalState Fc) horth
    have hdnonneg : 0 ≤ Q.decayFactor (t / 2) :=
      Q.decayFactor_nonneg (t / 2)
    have hrhsnonneg :
        0 ≤ Q.decayFactor (t / 2) * ‖Pn.physicalState Fc‖ :=
      mul_nonneg hdnonneg (norm_nonneg _)
    have hsq :
        ‖C.finiteOperator n (t / 2) (Pn.physicalState Fc)‖ ^ 2 ≤
          (Q.decayFactor (t / 2) * ‖Pn.physicalState Fc‖) ^ 2 := by
      nlinarith [norm_nonneg
        (C.finiteOperator n (t / 2) (Pn.physicalState Fc))]
    calc
      Pn.osQuadraticValue (Tn.carrierTranslation (t / 2) Fc) =
          ‖Pn.physicalState (Tn.carrierTranslation (t / 2) Fc)‖ ^ 2 := by
        rw [Pn.osQuadraticValue_eq_norm_sq, Pn.norm_physicalState]
      _ = ‖Pn.physicalState
            (Tn.toCarrierSemigroup.translate (t / 2) Fc)‖ ^ 2 := by
        simp only [
          PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.PositiveTimeObservableContractionSemigroup.toCarrierSemigroup]
      _ = ‖Tn.toCarrierSemigroup.physicalOperator (t / 2)
            (Pn.physicalState Fc)‖ ^ 2 := by
        rw [Tn.toCarrierSemigroup.physicalOperator_on_physicalState]
      _ = ‖C.finiteOperator n (t / 2) (Pn.physicalState Fc)‖ ^ 2 := by
        rfl
      _ ≤ (Q.decayFactor (t / 2) * ‖Pn.physicalState Fc‖) ^ 2 := hsq
      _ = Q.quadraticDecayFactor t * Pn.osQuadraticValue Fc := by
        rw [quadraticDecayFactor, Pn.osQuadraticValue_eq_norm_sq,
          Pn.norm_physicalState]
        ring

/-- The recovered half-time quadratic estimate gives the reflected OS
bilinear certificate. -/
noncomputable def toApproximatingReflectedQuadraticGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingNonnegativeVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingReflectedQuadraticGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.toApproximatingHalfQuadraticGapCertificate
    |>.toApproximatingReflectedQuadraticGapCertificate

/-- The completed nonnegative vacuum norm-decay certificate recovers the actual
finite periodic `SU(N)` Wilson Gibbs reflected-integral decay certificate. -/
noncomputable def toApproximatingFiniteIntegralGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingNonnegativeVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingFiniteIntegralGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C where
  mass := Q.mass
  mass_pos := Q.mass_pos
  quadraticDecayFactor := Q.quadraticDecayFactor
  quadraticDecayFactor_nonneg := Q.quadraticDecayFactor_nonneg
  slope_tendsto := by
    simpa only [Q.sqrt_quadraticDecayFactor_add_self] using Q.slope_tendsto
  exchange := Q.exchange
  finite_integral_decay := by
    intro n t
    dsimp only
    intro F
    rw [← physical_yang_mills_evenPeriodicWilsonOS_osQuadraticValue_eq_finiteReflectedIntegral,
      ← physical_yang_mills_evenPeriodicWilsonOS_osQuadraticValue_eq_finiteReflectedIntegral]
    exact Q.toApproximatingHalfQuadraticGapCertificate.finite_half_quadratic_decay n t F

end PhysicalYangMillsEvenPeriodicWilsonOSApproximatingNonnegativeVacuumGapCertificate

end MathlibAnalytic
end MGAP4D

end
