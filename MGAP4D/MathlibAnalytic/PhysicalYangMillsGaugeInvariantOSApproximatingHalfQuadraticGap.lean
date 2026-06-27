import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingReflectedQuadraticGap
import Mathlib.Tactic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace PositiveTimeObservableContractionSemigroup

/-- For a reflection/time-exchange symmetric OS semigroup, the diagonal
coefficient at time `t` is the OS quadratic value of the half-time translated
observable. -/
theorem osBilinForm_carrierTranslation_eq_osQuadraticValue_half
    (T : P.PositiveTimeObservableContractionSemigroup)
    (hExchange : T.ReflectionTimeTranslationExchange)
    (t : NNReal) (F : P.Carrier) :
    D.osBilinForm P.omega
        (P.toPositiveTime (T.carrierTranslation t F))
        (P.toPositiveTime F) =
      P.osQuadraticValue (T.carrierTranslation (t / 2) F) := by
  have hhalf : t / 2 + t / 2 = t := by
    ext
    norm_num <;> ring
  have hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric :=
    hExchange.toPhysicalSemigroup_isInnerSymmetric
  calc
    D.osBilinForm P.omega
        (P.toPositiveTime (T.carrierTranslation t F))
        (P.toPositiveTime F) =
      inner ℝ (T.toPhysicalSemigroup.operator t (P.physicalState F))
        (P.physicalState F) := by
      exact (T.inner_operator_physicalState_eq_osBilinForm t F).symm
    _ = ‖T.toPhysicalSemigroup.operator (t / 2) (P.physicalState F)‖ ^ 2 := by
      rw [← hhalf]
      exact
        (T.toPhysicalSemigroup.operator_norm_sq_eq_inner_operator_add_self
          hSymmetric (t / 2) (P.physicalState F)).symm
    _ = ‖P.physicalState (T.carrierTranslation (t / 2) F)‖ ^ 2 := by
      change
        ‖T.toCarrierSemigroup.physicalOperator (t / 2)
            (P.physicalState F)‖ ^ 2 = _
      rw [T.toCarrierSemigroup.physicalOperator_on_physicalState]
    _ = ‖T.carrierTranslation (t / 2) F‖ ^ 2 := by
      rw [P.norm_physicalState]
    _ = P.osQuadraticValue (T.carrierTranslation (t / 2) F) := by
      exact
        (P.osQuadraticValue_eq_norm_sq
          (T.carrierTranslation (t / 2) F)).symm

end PositiveTimeObservableContractionSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

/-- A finite Wilson OS gap certificate reduced to pure half-time OS quadratic
values of centered carrier observables.

This formulation is directly compatible with the existing finite-volume
reflection-positivity bridge, because both sides are evaluations of
`Theta(F) * F` for positive-time observables. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHalfQuadraticGapCertificate
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
      S D halfExtent N hN beta hbeta B hInvariant) where
  mass : ℝ
  mass_pos : 0 < mass
  quadraticDecayFactor : NNReal → ℝ
  quadraticDecayFactor_nonneg :
    ∀ t, 0 ≤ quadraticDecayFactor t
  slope_tendsto :
    Tendsto
      (fun t : NNReal =>
        (t : ℝ)⁻¹ *
          (1 - Real.sqrt (quadraticDecayFactor (t + t))))
      (nhdsWithin 0 (Ioi 0))
      (nhds mass)
  exchange : ∀ n,
    PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.PositiveTimeObservableContractionSemigroup.ReflectionTimeTranslationExchange
      (C.toPositiveTimeObservableContractionSemigroup n)
  finite_half_quadratic_decay :
    ∀ (n : ℕ) (t : NNReal),
      let Pn :=
        physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta B hInvariant n
      let Tn := C.toPositiveTimeObservableContractionSemigroup n
      ∀ F : Pn.Carrier,
        Pn.osQuadraticValue
            (Tn.carrierTranslation (t / 2) (Pn.vacuumCenteredCarrier F)) ≤
          quadraticDecayFactor t *
            Pn.osQuadraticValue (Pn.vacuumCenteredCarrier F)

namespace PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHalfQuadraticGapCertificate

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

/-- The half-time quadratic estimate generates the reflected bilinear
certificate. -/
noncomputable def toApproximatingReflectedQuadraticGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHalfQuadraticGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingReflectedQuadraticGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C where
  mass := Q.mass
  mass_pos := Q.mass_pos
  quadraticDecayFactor := Q.quadraticDecayFactor
  quadraticDecayFactor_nonneg := Q.quadraticDecayFactor_nonneg
  slope_tendsto := Q.slope_tendsto
  exchange := Q.exchange
  finite_reflected_quadratic_decay := by
    intro n t F
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n
    let Tn := C.toPositiveTimeObservableContractionSemigroup n
    calc
      D.osBilinForm Pn.omega
          (Pn.toPositiveTime
            (Tn.carrierTranslation t (Pn.vacuumCenteredCarrier F)))
          (Pn.toPositiveTime (Pn.vacuumCenteredCarrier F)) =
        Pn.osQuadraticValue
          (Tn.carrierTranslation (t / 2) (Pn.vacuumCenteredCarrier F)) := by
        exact
          Tn.osBilinForm_carrierTranslation_eq_osQuadraticValue_half
            (Q.exchange n) t (Pn.vacuumCenteredCarrier F)
      _ ≤ Q.quadraticDecayFactor t *
          Pn.osQuadraticValue (Pn.vacuumCenteredCarrier F) :=
        Q.finite_half_quadratic_decay n t F

/-- The half-time finite Wilson OS quadratic certificate therefore produces the
completed finite-volume norm-decay certificate. -/
noncomputable def toApproximatingVacuumGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHalfQuadraticGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.toApproximatingReflectedQuadraticGapCertificate
    |>.toApproximatingVacuumGapCertificate

end PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHalfQuadraticGapCertificate

end MathlibAnalytic
end MGAP4D

end
