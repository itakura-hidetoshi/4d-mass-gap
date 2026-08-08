import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSBoundaryMomentLinearIsometry
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace InnerProduct

namespace MGAP4D
namespace MathlibAnalytic

local instance positiveHalfCoherenceSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance positiveHalfCoherenceSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance positiveHalfCoherenceSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance positiveHalfCoherenceSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance positiveHalfCoherenceSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance positiveHalfCoherenceSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance positiveHalfCoherenceOpenHalfHaarProbability (H N : ℕ) :
    IsProbabilityMeasure (periodicHypercubicEvenOpenHalfHaarMeasure H N) := by
  dsimp [periodicHypercubicEvenOpenHalfHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
  infer_instance

/-- Upstream algebraic coherence for the actual finite positive-half pullback.

The present weak-star Wilson bridge chooses a finite bridge independently for
each physical quadratic observable.  The exact missing information needed to
make the associated boundary moment linear is that the resulting *raw bounded
continuous positive-half observable* respect addition and real scalar
multiplication on the OS carrier.

No norm, integrability, decay, coercivity, or mass hypothesis appears here. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfPullbackLinearCoherence
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

namespace PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfPullbackLinearCoherence

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

/-- The coherent raw finite positive-half observable is a real-linear map from
the actual OS carrier into bounded continuous open-half observables. -/
noncomputable def positiveHalfObservableLinearMap
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfPullbackLinearCoherence
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

@[simp] theorem positiveHalfObservableLinearMap_apply
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfPullbackLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    Q.positiveHalfObservableLinearMap n F =
      physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
        S D halfExtent N hN beta hbeta B hInvariant n F :=
  rfl

/-- Composing the raw pullback with Mathlib's canonical bounded-continuous to
`L²` continuous linear map gives the actual open-half feature map used by
`A_φ†`. -/
noncomputable def positiveHalfObservableL2LinearMap
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfPullbackLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ) :
    (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier →ₗ[ℝ]
      PhysicalYangMillsEvenPeriodicWilsonOSOpenHalfFeatureL2 halfExtent N n :=
  (BoundedContinuousFunction.toLp
      (E := ℝ) 2
      (periodicHypercubicEvenOpenHalfHaarMeasure (halfExtent n) N) ℝ).toLinearMap.comp
    (Q.positiveHalfObservableLinearMap n)

@[simp] theorem positiveHalfObservableL2LinearMap_apply
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfPullbackLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    Q.positiveHalfObservableL2LinearMap n F =
      physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservableL2
        S D halfExtent N hN beta hbeta B hInvariant n F := by
  rfl

/-- Raw pullback additivity descends canonically to the actual open-half Haar
`L²` feature vector. -/
theorem finitePositiveHalfObservableL2_add
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfPullbackLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ)
    (F G : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservableL2
        S D halfExtent N hN beta hbeta B hInvariant n (F + G) =
      physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservableL2
          S D halfExtent N hN beta hbeta B hInvariant n F +
        physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservableL2
          S D halfExtent N hN beta hbeta B hInvariant n G := by
  change Q.positiveHalfObservableL2LinearMap n (F + G) =
    Q.positiveHalfObservableL2LinearMap n F +
      Q.positiveHalfObservableL2LinearMap n G
  exact (Q.positiveHalfObservableL2LinearMap n).map_add F G

/-- Raw pullback homogeneity descends canonically to the actual open-half Haar
`L²` feature vector. -/
theorem finitePositiveHalfObservableL2_smul
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfPullbackLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ) (r : ℝ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservableL2
        S D halfExtent N hN beta hbeta B hInvariant n (r • F) =
      r • physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservableL2
        S D halfExtent N hN beta hbeta B hInvariant n F := by
  change Q.positiveHalfObservableL2LinearMap n (r • F) =
    r • Q.positiveHalfObservableL2LinearMap n F
  exact (Q.positiveHalfObservableL2LinearMap n).map_smul r F

/-- Upstream positive-half pullback coherence automatically generates the
minimal boundary-moment coherence isolated in #1470.

The proof does not reopen any Wilson integral.  It uses the exact theorem
`m_F = A_φ† u_F` and linearity of the already-constructed adjoint synthesis
operator. -/
noncomputable def toBoundaryMomentLinearCoherence
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfPullbackLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant where
  map_add := by
    intro n F G
    let A :=
      physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
        halfExtent N hN beta hbeta n
    calc
      physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S D halfExtent N hN beta hbeta B hInvariant n (F + G) =
        A
          (physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservableL2
            S D halfExtent N hN beta hbeta B hInvariant n (F + G)) := by
        simpa [A] using
          physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2_eq_actualSynthesis
            S D halfExtent N hN beta hbeta B hInvariant n (F + G)
      _ = A
          (physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservableL2
              S D halfExtent N hN beta hbeta B hInvariant n F +
            physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservableL2
              S D halfExtent N hN beta hbeta B hInvariant n G) := by
        rw [Q.finitePositiveHalfObservableL2_add n F G]
      _ = A
            (physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservableL2
              S D halfExtent N hN beta hbeta B hInvariant n F) +
          A
            (physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservableL2
              S D halfExtent N hN beta hbeta B hInvariant n G) := by
        exact A.map_add _ _
      _ = physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
            S D halfExtent N hN beta hbeta B hInvariant n F +
          physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
            S D halfExtent N hN beta hbeta B hInvariant n G := by
        rw [← physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2_eq_actualSynthesis
              S D halfExtent N hN beta hbeta B hInvariant n F,
          ← physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2_eq_actualSynthesis
              S D halfExtent N hN beta hbeta B hInvariant n G]
  map_smul := by
    intro n r F
    let A :=
      physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
        halfExtent N hN beta hbeta n
    calc
      physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S D halfExtent N hN beta hbeta B hInvariant n (r • F) =
        A
          (physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservableL2
            S D halfExtent N hN beta hbeta B hInvariant n (r • F)) := by
        simpa [A] using
          physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2_eq_actualSynthesis
            S D halfExtent N hN beta hbeta B hInvariant n (r • F)
      _ = A
          (r • physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservableL2
            S D halfExtent N hN beta hbeta B hInvariant n F) := by
        rw [Q.finitePositiveHalfObservableL2_smul n r F]
      _ = r • A
          (physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservableL2
            S D halfExtent N hN beta hbeta B hInvariant n F) := by
        exact A.map_smul r _
      _ = r • physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S D halfExtent N hN beta hbeta B hInvariant n F := by
        rw [← physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2_eq_actualSynthesis
              S D halfExtent N hN beta hbeta B hInvariant n F]

/-- Therefore raw finite positive-half pullback coherence already produces a
canonical linear-isometric embedding of the actual OS pre-Hilbert carrier into
shared-boundary Haar `L²`. -/
noncomputable def boundaryMomentLinearIsometry
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfPullbackLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ) :
    (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier →ₗᵢ[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N :=
  Q.toBoundaryMomentLinearCoherence.linearIsometry n

@[simp] theorem boundaryMomentLinearIsometry_apply
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfPullbackLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    Q.boundaryMomentLinearIsometry n F =
      physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        S D halfExtent N hN beta hbeta B hInvariant n F :=
  rfl

/-- The same isometry is exactly the composition of the coherent open-half
pullback with actual Wilson adjoint synthesis, pointwise on the OS carrier. -/
theorem boundaryMomentLinearIsometry_apply_eq_actualSynthesis
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfPullbackLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    Q.boundaryMomentLinearIsometry n F =
      physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
        halfExtent N hN beta hbeta n
        (Q.positiveHalfObservableL2LinearMap n F) := by
  rw [boundaryMomentLinearIsometry_apply,
    physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2_eq_actualSynthesis,
    positiveHalfObservableL2LinearMap_apply]

end PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfPullbackLinearCoherence

end MathlibAnalytic
end MGAP4D

end