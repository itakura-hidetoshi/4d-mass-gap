import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalBoundaryFiniteIntegralIdentification
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSExponentialGapSlope
import Mathlib.Tactic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

/-- Corrected model-facing exponential finite-Wilson gap package.

The only quantitative input is imposed on the actual finite reflected Wilson
integral of vacuum-centered carrier observables:

`(1 - exp (-m t)) I_n(F_c) <= I_n(F_c) - I_n(T_{n,t/2} F_c)`.

This deliberately avoids the obsolete all-boundary strict-contraction
formulation.  The raw OS carrier is dense in the completed finite physical
Hilbert space, so the existing observable-core and finite-integral transfer
machinery generates the completed vacuum-sector estimate downstream. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSActualFiniteIntegralExponentialGapCertificate
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
  exchange : ∀ n,
    PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.PositiveTimeObservableContractionSemigroup.ReflectionTimeTranslationExchange
      (C.toPositiveTimeObservableContractionSemigroup n)
  finite_integral_exponential_defect :
    ∀ (n : ℕ) (t : NNReal),
      let Pn :=
        physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta B hInvariant n
      let Tn := C.toPositiveTimeObservableContractionSemigroup n
      ∀ F : Pn.Carrier,
        (1 - Real.exp (-mass * (t : ℝ))) *
            physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
              S D halfExtent N hN beta hbeta B hInvariant n
              (Pn.vacuumCenteredCarrier F) ≤
          physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
              S D halfExtent N hN beta hbeta B hInvariant n
              (Pn.vacuumCenteredCarrier F) -
            physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
              S D halfExtent N hN beta hbeta B hInvariant n
              (Tn.carrierTranslation (t / 2)
                (Pn.vacuumCenteredCarrier F))

namespace PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence

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

/-- The actual finite reflected-integral exponential defect is exactly the
canonical boundary squared-norm defect on the dense centered physical boundary
image.

The boundary time is `t`, while the corresponding finite physical transfer is
at time `t / 2`, matching the canonical definition `K_t = J T_{t/2} J†`. -/
theorem
    finiteReflectedIntegral_exponential_defect_iff_canonicalBoundaryTransfer_centeredBoundaryMoment_exponential_defect
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ) (t : NNReal) (mass : ℝ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n
    let Tn := C.toPositiveTimeObservableContractionSemigroup n
    (1 - Real.exp (-mass * (t : ℝ))) *
          physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
            S D halfExtent N hN beta hbeta B hInvariant n
            (Pn.vacuumCenteredCarrier F) ≤
        physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
            S D halfExtent N hN beta hbeta B hInvariant n
            (Pn.vacuumCenteredCarrier F) -
          physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
            S D halfExtent N hN beta hbeta B hInvariant n
            (Tn.carrierTranslation (t / 2)
              (Pn.vacuumCenteredCarrier F)) ↔
    (1 - Real.exp (-mass * (t : ℝ))) *
          ‖physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
            S D halfExtent N hN beta hbeta B hInvariant n
            (Pn.vacuumCenteredCarrier F)‖ ^ 2 ≤
        ‖physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
            S D halfExtent N hN beta hbeta B hInvariant n
            (Pn.vacuumCenteredCarrier F)‖ ^ 2 -
          ‖L.canonicalBoundaryTransfer C n t
            (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
              S D halfExtent N hN beta hbeta B hInvariant n
              (Pn.vacuumCenteredCarrier F))‖ ^ 2 := by
  dsimp only
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n
  let Tn := C.toPositiveTimeObservableContractionSemigroup n
  have htranslated :
      ‖L.canonicalBoundaryTransfer C n t
          (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
            S D halfExtent N hN beta hbeta B hInvariant n
            (Pn.vacuumCenteredCarrier F))‖ ^ 2 =
        physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
          S D halfExtent N hN beta hbeta B hInvariant n
          (Tn.carrierTranslation (t / 2)
            (Pn.vacuumCenteredCarrier F)) := by
    rw [L.canonicalBoundaryTransfer_canonicalBoundaryMoment_intertwining
      C n t (Pn.vacuumCenteredCarrier F)]
    exact
      physical_yang_mills_evenPeriodicWilsonOS_canonicalBoundaryMomentL2_norm_sq_eq_finiteReflectedIntegral
        S D halfExtent N hN beta hbeta B hInvariant n
        (Tn.carrierTranslation (t / 2) (Pn.vacuumCenteredCarrier F))
  have hinitial :=
    physical_yang_mills_evenPeriodicWilsonOS_canonicalBoundaryMomentL2_norm_sq_eq_finiteReflectedIntegral
      S D halfExtent N hN beta hbeta B hInvariant n
      (Pn.vacuumCenteredCarrier F)
  constructor
  · intro h
    calc
      (1 - Real.exp (-mass * (t : ℝ))) *
          ‖physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
            S D halfExtent N hN beta hbeta B hInvariant n
            (Pn.vacuumCenteredCarrier F)‖ ^ 2 =
        (1 - Real.exp (-mass * (t : ℝ))) *
          physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
            S D halfExtent N hN beta hbeta B hInvariant n
            (Pn.vacuumCenteredCarrier F) := by
          rw [hinitial]
      _ ≤
        physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
            S D halfExtent N hN beta hbeta B hInvariant n
            (Pn.vacuumCenteredCarrier F) -
          physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
            S D halfExtent N hN beta hbeta B hInvariant n
            (Tn.carrierTranslation (t / 2)
              (Pn.vacuumCenteredCarrier F)) := h
      _ =
        ‖physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
            S D halfExtent N hN beta hbeta B hInvariant n
            (Pn.vacuumCenteredCarrier F)‖ ^ 2 -
          ‖L.canonicalBoundaryTransfer C n t
            (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
              S D halfExtent N hN beta hbeta B hInvariant n
              (Pn.vacuumCenteredCarrier F))‖ ^ 2 := by
          rw [hinitial, htranslated]
  · intro h
    calc
      (1 - Real.exp (-mass * (t : ℝ))) *
          physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
            S D halfExtent N hN beta hbeta B hInvariant n
            (Pn.vacuumCenteredCarrier F) =
        (1 - Real.exp (-mass * (t : ℝ))) *
          ‖physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
            S D halfExtent N hN beta hbeta B hInvariant n
            (Pn.vacuumCenteredCarrier F)‖ ^ 2 := by
          rw [hinitial]
      _ ≤
        ‖physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
            S D halfExtent N hN beta hbeta B hInvariant n
            (Pn.vacuumCenteredCarrier F)‖ ^ 2 -
          ‖L.canonicalBoundaryTransfer C n t
            (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
              S D halfExtent N hN beta hbeta B hInvariant n
              (Pn.vacuumCenteredCarrier F))‖ ^ 2 := h
      _ =
        physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
            S D halfExtent N hN beta hbeta B hInvariant n
            (Pn.vacuumCenteredCarrier F) -
          physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
            S D halfExtent N hN beta hbeta B hInvariant n
            (Tn.carrierTranslation (t / 2)
              (Pn.vacuumCenteredCarrier F)) := by
          rw [hinitial, htranslated]

end PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence

namespace PhysicalYangMillsEvenPeriodicWilsonOSActualFiniteIntegralExponentialGapCertificate

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

/-- Exponential finite-time Poincaré defect implies the equivalent multiplicative
reflected-integral decay with factor `exp (-mass * t)`. -/
theorem finite_integral_exponential_decay
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSActualFiniteIntegralExponentialGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (n : ℕ) (t : NNReal)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n
    let Tn := C.toPositiveTimeObservableContractionSemigroup n
    physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
        S D halfExtent N hN beta hbeta B hInvariant n
        (Tn.carrierTranslation (t / 2) (Pn.vacuumCenteredCarrier F)) ≤
      Real.exp (-Q.mass * (t : ℝ)) *
        physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
          S D halfExtent N hN beta hbeta B hInvariant n
          (Pn.vacuumCenteredCarrier F) := by
  dsimp only
  have h := Q.finite_integral_exponential_defect n t F
  nlinarith

/-- The model-facing exponential finite-integral package generates exactly the
existing finite-integral gap certificate, with
`quadraticDecayFactor t = exp (-mass * t)`.

Consequently the positive small-time slope is theorem-generated rather than
stored as an additional assumption. -/
noncomputable def toApproximatingFiniteIntegralGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSActualFiniteIntegralExponentialGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingFiniteIntegralGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C where
  mass := Q.mass
  mass_pos := Q.mass_pos
  quadraticDecayFactor := fun t => Real.exp (-Q.mass * (t : ℝ))
  quadraticDecayFactor_nonneg :=
    exponential_quadraticDecayFactor_nonneg Q.mass
  slope_tendsto :=
    exponential_quadraticDecayFactor_slope_tendsto Q.mass
  exchange := Q.exchange
  finite_integral_decay := by
    intro n t
    dsimp only
    intro F
    exact Q.finite_integral_exponential_decay n t F

/-- The same actual finite reflected-integral exponential defect therefore
produces the completed finite Wilson vacuum-sector norm-decay certificate. -/
noncomputable def toApproximatingVacuumGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSActualFiniteIntegralExponentialGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.toApproximatingFiniteIntegralGapCertificate
    |>.toApproximatingVacuumGapCertificate

/-- Under the same actual finite-integral defect, the corrected canonical
boundary transfer satisfies the exponential Poincaré defect on every centered
canonical boundary moment in the dense physical image.  No assertion is made
on the full boundary space, which contains the fixed vacuum. -/
theorem canonicalBoundaryTransfer_centeredBoundaryMoment_exponential_defect
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSActualFiniteIntegralExponentialGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ) (t : NNReal)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n
    (1 - Real.exp (-Q.mass * (t : ℝ))) *
          ‖physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
            S D halfExtent N hN beta hbeta B hInvariant n
            (Pn.vacuumCenteredCarrier F)‖ ^ 2 ≤
        ‖physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
            S D halfExtent N hN beta hbeta B hInvariant n
            (Pn.vacuumCenteredCarrier F)‖ ^ 2 -
          ‖L.canonicalBoundaryTransfer C n t
            (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
              S D halfExtent N hN beta hbeta B hInvariant n
              (Pn.vacuumCenteredCarrier F))‖ ^ 2 := by
  dsimp only
  have h := Q.finite_integral_exponential_defect n t F
  exact
    (L.finiteReflectedIntegral_exponential_defect_iff_canonicalBoundaryTransfer_centeredBoundaryMoment_exponential_defect
      C n t Q.mass F).mp h

end PhysicalYangMillsEvenPeriodicWilsonOSActualFiniteIntegralExponentialGapCertificate

end MathlibAnalytic
end MGAP4D

end
