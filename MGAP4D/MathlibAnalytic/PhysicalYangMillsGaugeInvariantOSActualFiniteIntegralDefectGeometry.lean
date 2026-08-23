import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSActualFiniteIntegralExponentialGap
import Mathlib.Tactic

noncomputable section

open MeasureTheory Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

/-- The finite-time Dirichlet defect of one actual finite periodic Wilson
reflected integral.

The time parameter here is the physical finite-OS transfer time.  Thus
`D_n(t,F) = I_n(F) - I_n(T_{n,t}F)`.  The exponential gap interface from #2022
is exactly a lower bound on `D_n(t/2,F_c)` for vacuum-centered carriers. -/
noncomputable def physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegralDefect
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
    (n : ℕ) (t : NNReal)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) : ℝ :=
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n
  let Tn := C.toPositiveTimeObservableContractionSemigroup n
  physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
      S D halfExtent N hN beta hbeta B hInvariant n F -
    physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
      S D halfExtent N hN beta hbeta B hInvariant n
      (Tn.carrierTranslation t F)

namespace PhysicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegralDefect

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

/-- The actual reflected-integral defect is exactly the loss of squared OS
carrier norm under finite transfer. -/
theorem eq_carrier_norm_sq_sub
    (n : ℕ) (t : NNReal)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegralDefect
        S D halfExtent N hN beta hbeta B hInvariant C n t F =
      ‖F‖ ^ 2 -
        ‖(C.toPositiveTimeObservableContractionSemigroup n).carrierTranslation
          t F‖ ^ 2 := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n
  let Tn := C.toPositiveTimeObservableContractionSemigroup n
  change
    physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
        S D halfExtent N hN beta hbeta B hInvariant n F -
      physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
        S D halfExtent N hN beta hbeta B hInvariant n
        (Tn.carrierTranslation t F) =
      ‖F‖ ^ 2 - ‖Tn.carrierTranslation t F‖ ^ 2
  rw [← physical_yang_mills_evenPeriodicWilsonOS_osQuadraticValue_eq_finiteReflectedIntegral
        S D halfExtent N hN beta hbeta B hInvariant n F,
      ← physical_yang_mills_evenPeriodicWilsonOS_osQuadraticValue_eq_finiteReflectedIntegral
        S D halfExtent N hN beta hbeta B hInvariant n
        (Tn.carrierTranslation t F),
      Pn.osQuadraticValue_eq_norm_sq,
      Pn.osQuadraticValue_eq_norm_sq]

/-- Every actual finite reflected-integral defect is nonnegative.  This is a
model-side scalar form of the already constructed finite OS contraction and
uses no gap hypothesis. -/
theorem nonneg
    (n : ℕ) (t : NNReal)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    0 ≤
      physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegralDefect
        S D halfExtent N hN beta hbeta B hInvariant C n t F := by
  let Tn := C.toPositiveTimeObservableContractionSemigroup n
  rw [eq_carrier_norm_sq_sub]
  have hnorm : ‖Tn.carrierTranslation t F‖ ≤ ‖F‖ :=
    Tn.carrierTranslation_norm_le t F
  nlinarith [norm_nonneg F, norm_nonneg (Tn.carrierTranslation t F)]

/-- The same scalar defect is exactly the squared norm defect of the completed
finite physical OS transfer on the represented state. -/
theorem eq_physical_norm_sq_sub
    (n : ℕ) (t : NNReal)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n
    physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegralDefect
        S D halfExtent N hN beta hbeta B hInvariant C n t F =
      ‖Pn.physicalState F‖ ^ 2 -
        ‖C.finiteOperator n t (Pn.physicalState F)‖ ^ 2 := by
  dsimp only
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n
  let Tn := C.toPositiveTimeObservableContractionSemigroup n
  rw [eq_carrier_norm_sq_sub]
  rw [PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence.finiteOperator_on_physicalState
    C n t F]
  rw [Pn.norm_physicalState, Pn.norm_physicalState]

/-- Finite reflected-integral defects satisfy the exact semigroup cocycle law.
The loss accumulated over `s+t` is the loss over `t`, followed by the loss over
`s` starting from the time-`t` translated carrier. -/
theorem add
    (n : ℕ) (s t : NNReal)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    let Tn := C.toPositiveTimeObservableContractionSemigroup n
    physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegralDefect
        S D halfExtent N hN beta hbeta B hInvariant C n (s + t) F =
      physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegralDefect
          S D halfExtent N hN beta hbeta B hInvariant C n t F +
        physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegralDefect
          S D halfExtent N hN beta hbeta B hInvariant C n s
          (Tn.carrierTranslation t F) := by
  dsimp only
  let Tn := C.toPositiveTimeObservableContractionSemigroup n
  rw [eq_carrier_norm_sq_sub, eq_carrier_norm_sq_sub,
    eq_carrier_norm_sq_sub]
  rw [Tn.carrierTranslation_add s t F]
  ring

/-- Under linear boundary-moment coherence, the actual finite reflected-integral
defect is exactly the squared norm defect of the canonical shared-boundary
transfer.  Boundary time is twice physical time because
`K_{n,2t} = J_n T_{n,t} J_n†` on the physical image. -/
theorem eq_canonicalBoundaryTransfer_norm_sq_sub
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ) (t : NNReal)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegralDefect
        S D halfExtent N hN beta hbeta B hInvariant C n t F =
      ‖physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S D halfExtent N hN beta hbeta B hInvariant n F‖ ^ 2 -
        ‖L.canonicalBoundaryTransfer C n (2 * t)
          (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
            S D halfExtent N hN beta hbeta B hInvariant n F)‖ ^ 2 := by
  let Tn := C.toPositiveTimeObservableContractionSemigroup n
  have htime : (2 * t) / 2 = t := by
    ext
    norm_num
  have hinter :=
    L.canonicalBoundaryTransfer_canonicalBoundaryMoment_intertwining
      C n (2 * t) F
  rw [htime] at hinter
  calc
    physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegralDefect
        S D halfExtent N hN beta hbeta B hInvariant C n t F =
      ‖F‖ ^ 2 - ‖Tn.carrierTranslation t F‖ ^ 2 :=
        eq_carrier_norm_sq_sub n t F
    _ =
      ‖physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S D halfExtent N hN beta hbeta B hInvariant n F‖ ^ 2 -
        ‖physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S D halfExtent N hN beta hbeta B hInvariant n
          (Tn.carrierTranslation t F)‖ ^ 2 := by
      rw [physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2_norm,
        physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2_norm]
    _ =
      ‖physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S D halfExtent N hN beta hbeta B hInvariant n F‖ ^ 2 -
        ‖L.canonicalBoundaryTransfer C n (2 * t)
          (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
            S D halfExtent N hN beta hbeta B hInvariant n F)‖ ^ 2 := by
      rw [hinter]

/-- The #2022 exponential finite-integral certificate is precisely a lower
bound on the named nonnegative defect functional at half physical time. -/
theorem exponential_lower_bound
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSActualFiniteIntegralExponentialGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (n : ℕ) (t : NNReal)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n
    (1 - Real.exp (-Q.mass * (t : ℝ))) *
        physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
          S D halfExtent N hN beta hbeta B hInvariant n
          (Pn.vacuumCenteredCarrier F) ≤
      physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegralDefect
        S D halfExtent N hN beta hbeta B hInvariant C n (t / 2)
        (Pn.vacuumCenteredCarrier F) := by
  dsimp only
  simpa [physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegralDefect] using
    Q.finite_integral_exponential_defect n t F

end PhysicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegralDefect

end MathlibAnalytic
end MGAP4D

end
