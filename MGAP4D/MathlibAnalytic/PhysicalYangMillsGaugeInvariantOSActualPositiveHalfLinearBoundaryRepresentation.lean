import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSActualBoundaryMomentQuotientIsometry
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance actualPositiveHalfLinearSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance actualPositiveHalfLinearSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance actualPositiveHalfLinearSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance actualPositiveHalfLinearSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance actualPositiveHalfLinearSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance actualPositiveHalfLinearSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance actualPositiveHalfLinearOpenHalfHaarProbability (H N : ℕ) :
    IsProbabilityMeasure (periodicHypercubicEvenOpenHalfHaarMeasure H N) := by
  dsimp [periodicHypercubicEvenOpenHalfHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
  infer_instance

/-- Algebraic coherence of the actual finite-Wilson positive-half pullbacks.

This is strictly closer to the model than boundary-moment coherence.  It asks
only that the bounded-continuous positive-half observable already selected by
the finite Wilson pullback bridge respect addition and real scalar
multiplication on the Osterwalder--Schrader carrier.

The current abstract weak-star bridge does not generate these laws: its finite
bridge is selected independently for each quadratic observable.  A concrete
positive-time support/factorization theorem for one observable-independent
lattice pullback is the intended source of this datum. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservableLinearCoherence
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
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)) : Prop where
  map_add :
    ∀ (n : ℕ)
      (F G : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n).Carrier),
      physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
          S D halfExtent N hN beta hbeta B hInvariant n (F + G) =
        physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
            S D halfExtent N hN beta hbeta B hInvariant n F +
          physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
            S D halfExtent N hN beta hbeta B hInvariant n G
  map_smul :
    ∀ (n : ℕ) (r : ℝ)
      (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n).Carrier),
      physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
          S D halfExtent N hN beta hbeta B hInvariant n (r • F) =
        r • physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
          S D halfExtent N hN beta hbeta B hInvariant n F

namespace PhysicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservableLinearCoherence

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

/-- Bundle the actual bounded-continuous positive-half pullback as a real-linear
map on the OS carrier. -/
noncomputable def boundedContinuousLinearMap
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservableLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ) :
    (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier →ₗ[ℝ]
      BoundedContinuousFunction
        (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
          (halfExtent n) N) ℝ where
  toFun := fun F =>
    physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
      S D halfExtent N hN beta hbeta B hInvariant n F
  map_add' := Q.map_add n
  map_smul' := Q.map_smul n

@[simp] theorem boundedContinuousLinearMap_apply
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservableLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    Q.boundedContinuousLinearMap n F =
      physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
        S D halfExtent N hN beta hbeta B hInvariant n F :=
  rfl

/-- The actual positive-half pullback in Haar `L²`, obtained by composing the
coherent bounded-continuous map with Mathlib's canonical
`BoundedContinuousFunction.toLp` continuous linear map. -/
noncomputable def openHalfL2LinearMap
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservableLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ) :
    (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier →ₗ[ℝ]
      PhysicalYangMillsEvenPeriodicWilsonOSOpenHalfFeatureL2 halfExtent N n :=
  (BoundedContinuousFunction.toLp
      (E := ℝ) 2
      (periodicHypercubicEvenOpenHalfHaarMeasure (halfExtent n) N) ℝ).toLinearMap.comp
    (Q.boundedContinuousLinearMap n)

@[simp] theorem openHalfL2LinearMap_apply
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservableLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    Q.openHalfL2LinearMap n F =
      physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservableL2
        S D halfExtent N hN beta hbeta B hInvariant n F :=
  rfl

/-- Compose the coherent positive-half `L²` pullback with the actual Wilson
adjoint synthesis `A_φ†`.  This is the boundary representation generated by the
finite Wilson model, not an abstract boundary map. -/
noncomputable def boundaryMomentLinearMap
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservableLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ) :
    (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier →ₗ[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N :=
  (physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
      halfExtent N hN beta hbeta n).toLinearMap.comp
    (Q.openHalfL2LinearMap n)

/-- The synthesis-generated boundary map is exactly the canonical actual Wilson
boundary moment. -/
theorem boundaryMomentLinearMap_apply
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservableLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    Q.boundaryMomentLinearMap n F =
      physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        S D halfExtent N hN beta hbeta B hInvariant n F := by
  calc
    Q.boundaryMomentLinearMap n F =
        physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
          halfExtent N hN beta hbeta n
          (Q.openHalfL2LinearMap n F) := by
      rfl
    _ = physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
          halfExtent N hN beta hbeta n
          (physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservableL2
            S D halfExtent N hN beta hbeta B hInvariant n F) := by
      rw [Q.openHalfL2LinearMap_apply]
    _ = physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S D halfExtent N hN beta hbeta B hInvariant n F := by
      exact
        (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2_eq_actualSynthesis
          S D halfExtent N hN beta hbeta B hInvariant n F).symm

/-- Positive-half pullback coherence theorem-generates the older boundary-moment
linear coherence; no boundary linearity is assumed separately. -/
noncomputable def toBoundaryMomentLinearCoherence
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservableLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant where
  map_add := by
    intro n F G
    rw [← Q.boundaryMomentLinearMap_apply n (F + G)]
    rw [(Q.boundaryMomentLinearMap n).map_add]
    rw [Q.boundaryMomentLinearMap_apply n F, Q.boundaryMomentLinearMap_apply n G]
  map_smul := by
    intro n r F
    rw [← Q.boundaryMomentLinearMap_apply n (r • F)]
    rw [(Q.boundaryMomentLinearMap n).map_smul]
    rw [Q.boundaryMomentLinearMap_apply n F]

/-- The complete algebraic consequence: coherent actual positive-half pullbacks
embed the separated finite Wilson OS space real-linearly and isometrically into
the actual shared-boundary Haar `L²` representation. -/
noncomputable def toSeparatedBoundaryMomentLinearIsometry
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservableLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ) :
    (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Separated →ₗᵢ[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N :=
  Q.toBoundaryMomentLinearCoherence.separatedBoundaryMomentLinearIsometry n

@[simp] theorem toSeparatedBoundaryMomentLinearIsometry_mk
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservableLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    Q.toSeparatedBoundaryMomentLinearIsometry n (SeparationQuotient.mk F) =
      physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        S D halfExtent N hN beta hbeta B hInvariant n F := by
  exact
    Q.toBoundaryMomentLinearCoherence.separatedBoundaryMomentLinearIsometry_mk n F

end PhysicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservableLinearCoherence

end

end MathlibAnalytic
end MGAP4D
