import MGAP4D.MathlibAnalytic.PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
import MGAP4D.MathlibAnalytic.RealLinearIsometrySeparationCompletion

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace InnerProduct

namespace MGAP4D
namespace MathlibAnalytic

local instance boundarySeparationSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance boundarySeparationSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance boundarySeparationSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance boundarySeparationSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance boundarySeparationSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance boundarySeparationSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

namespace PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}

/-- The canonical Wilson boundary-moment isometry descends through the exact OS
zero-seminorm quotient.

This is theorem-generated from the carrier-level norm identity; no quotient
compatibility is supplied as physical input. -/
noncomputable def separatedBoundaryMomentLinearIsometry
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ) :
    (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Separated →ₗᵢ[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N :=
  realLinearIsometrySeparationQuotient
    (Q.boundaryMomentLinearIsometry hInvariant n)

@[simp] theorem separatedBoundaryMomentLinearIsometry_osClass
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    Q.separatedBoundaryMomentLinearIsometry hInvariant n
        ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).osClass F) =
      physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F := by
  rw [separatedBoundaryMomentLinearIsometry]
  change
    (realLinearIsometrySeparationQuotient
      (Q.boundaryMomentLinearIsometry hInvariant n))
      (SeparationQuotient.mk F) = _
  rw [realLinearIsometrySeparationQuotient_mk]
  rfl

/-- The separated Wilson boundary realization extends uniquely and
isometrically to the completed approximating OS physical Hilbert space.

`Ĵ_n : H_n^OS → L²(boundary Haar)`

is therefore an actual Mathlib linear isometry on the complete physical
carrier, not merely a dense-carrier construction. -/
noncomputable def physicalHilbertBoundaryMomentLinearIsometry
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ) :
    (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).PhysicalHilbert →ₗᵢ[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N :=
  realLinearIsometrySeparationCompletion
    (Q.boundaryMomentLinearIsometry hInvariant n)

/-- The completed boundary isometry agrees with the original canonical Wilson
boundary moment on every dense physical state represented by an OS carrier
observable. -/
@[simp] theorem physicalHilbertBoundaryMomentLinearIsometry_physicalState
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
        ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).physicalState F) =
      physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F := by
  rw [physicalHilbertBoundaryMomentLinearIsometry]
  exact realLinearIsometrySeparationCompletion_coe_mk
    (Q.boundaryMomentLinearIsometry hInvariant n) F

/-- On dense physical states, the completed OS-to-boundary isometry is still
exactly the actual Wilson adjoint synthesis `A_φ†` applied to the coherent
positive-half `L²` pullback. -/
theorem physicalHilbertBoundaryMomentLinearIsometry_physicalState_eq_actualSynthesis
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
        ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).physicalState F) =
      physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
        halfExtent N hN beta hbeta n
        (Q.positiveHalfL2LinearMap hInvariant n F) := by
  rw [Q.physicalHilbertBoundaryMomentLinearIsometry_physicalState,
    physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2_eq_actualSynthesis,
    Q.positiveHalfL2LinearMap_apply]

/-- The carrier-level half-time factorization from the coherent Wilson pullback
survives unchanged after passing to the completed physical Hilbert embedding.
For every dense state,

`A_φ† U_{n,t} F = Ĵ_n [T_n(t/2)F]`.

Thus quotienting and Hilbert completion create no new intertwining obligation. -/
theorem actualSynthesis_translatedPositiveHalfL2LinearMap_eq_physicalHilbertEmbedding
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
    (n : ℕ) (t : NNReal)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
        halfExtent N hN beta hbeta n
        (Q.translatedPositiveHalfL2LinearMap hInvariant C n t F) =
      Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
        ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).physicalState
          ((C.toPositiveTimeObservableContractionSemigroup n).carrierTranslation
            (t / 2) F)) := by
  rw [Q.physicalHilbertBoundaryMomentLinearIsometry_physicalState]
  exact
    Q.actualSynthesis_translatedPositiveHalfL2LinearMap_apply
      hInvariant C n t F

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end MathlibAnalytic
end MGAP4D

end