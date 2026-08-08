import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSPositiveHalfPullbackLinearCoherence

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace InnerProduct

namespace MGAP4D
namespace MathlibAnalytic

local instance coherentPullbackSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance coherentPullbackSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance coherentPullbackSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance coherentPullbackSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance coherentPullbackSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance coherentPullbackSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}

/-- The identification of the opaque OS carrier with the original positive-time
observable algebra is additive. -/
@[simp] theorem positiveTimeElement_add
    (P : D.OSPreHilbertData) (F G : P.Carrier) :
    P.positiveTimeElement (F + G) =
      P.positiveTimeElement F + P.positiveTimeElement G := by
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-- The identification of the opaque OS carrier with the original positive-time
observable algebra is real homogeneous. -/
@[simp] theorem positiveTimeElement_smul
    (P : D.OSPreHilbertData) (r : ℝ) (F : P.Carrier) :
    P.positiveTimeElement (r • F) = r • P.positiveTimeElement F := by
  apply Subtype.ext
  apply Subtype.ext
  rfl

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

/-- Coherent finite-Wilson pullback data at the positive-time observable level.

The older weak-star bridge chooses a complete finite bridge separately for each
quadratic observable.  That is sufficient for reflection positivity but leaves
two unrelated choice freedoms: the lattice-to-physical interpolation map may
depend on the observable, and the positive-half square root may be selected
independently for every observable.

This structure removes both freedoms at once:

* one interpolation map is fixed at each lattice scale;
* one real-linear map sends the full physical positive-time observable algebra
  to bounded continuous positive-half finite-Wilson observables;
* the reflected quadratic pullback identity is required for this common linear
  map.

No decay, coercivity, mass, integrability, or operator-norm estimate is added. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n) where
  interpolate :
    ∀ n,
      (PeriodicHypercubicEvenEdge (halfExtent n) →
        Matrix.specialUnitaryGroup (Fin N) ℂ) →
        S.Configuration
  interpolate_measurable : ∀ n, Measurable (interpolate n)
  approximatingMeasure_toMeasure_eq :
    ∀ n,
      (S.approximatingMeasure n : Measure S.Configuration) =
        Measure.map (interpolate n)
          (periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength (halfExtent n))
            N hN (beta n) (hbeta n)).gibbsMeasure
  positiveHalfPullback :
    ∀ n,
      D.positiveTimeSubalgebra →ₗ[ℝ]
        BoundedContinuousFunction
          (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
            (halfExtent n) N) ℝ
  quadraticObservable_pullback :
    ∀ n (F : D.positiveTimeSubalgebra) A,
      D.quadraticBoundedContinuousFunction F (interpolate n A) =
        periodicHypercubicEvenFullReflectedObservable
          (halfExtent n) (positiveHalfPullback n F) A

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

/-- Forget coherence and recover the previously used per-observable weak-star
bridge.  Every generated finite bridge shares the same interpolation map and
uses the common linear positive-half pullback. -/
noncomputable def toWeakStarBridge
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta) :
    PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta where
  finiteBridge := fun F =>
    { interpolate := Q.interpolate
      interpolate_measurable := Q.interpolate_measurable
      positiveHalfObservable := fun n => Q.positiveHalfPullback n F
      approximatingMeasure_toMeasure_eq := Q.approximatingMeasure_toMeasure_eq
      quadraticObservable_pullback := fun n A =>
        Q.quadraticObservable_pullback n F A }

@[simp] theorem toWeakStarBridge_positiveHalfObservable
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (F : D.positiveTimeSubalgebra) (n : ℕ) :
    ((Q.toWeakStarBridge.finiteBridge F).positiveHalfObservable n) =
      Q.positiveHalfPullback n F :=
  rfl

@[simp] theorem toWeakStarBridge_interpolate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (F : D.positiveTimeSubalgebra) (n : ℕ) :
    (Q.toWeakStarBridge.finiteBridge F).interpolate n = Q.interpolate n :=
  rfl

/-- The coherent bridge retains the existing theorem-generated finite Wilson
reflection positivity. -/
theorem approximating_weakStarReflectionPositive
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (n : ℕ) :
    D.WeakStarReflectionPositive
      (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n) :=
  physical_yang_mills_evenPeriodicWilsonOS_approximating_weakStarReflectionPositive
    S D halfExtent N hN beta hbeta Q.toWeakStarBridge n

/-- The coherent bridge also retains continuum reflection positivity. -/
theorem continuum_weakStarReflectionPositive
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta) :
    D.WeakStarReflectionPositive
      (physicalYangMillsContinuumGaugeInvariantWeakStarState S) :=
  physical_yang_mills_evenPeriodicWilsonOS_continuum_weakStarReflectionPositive
    S D halfExtent N hN beta hbeta Q.toWeakStarBridge

/-- For the OS carrier generated from the coherent bridge, the actual finite
positive-half observable is definitionally the common linear pullback of its
positive-time observable. -/
@[simp] theorem finitePositiveHalfObservable_eq_positiveHalfPullback
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F =
      Q.positiveHalfPullback n
        ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).positiveTimeElement F) :=
  rfl

/-- A common positive-time linear pullback automatically generates the raw
positive-half coherence isolated previously. -/
noncomputable def toPositiveHalfPullbackLinearCoherence
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)) :
    PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfPullbackLinearCoherence
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant where
  map_add := by
    intro n F G
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    change Q.positiveHalfPullback n (Pn.positiveTimeElement (F + G)) =
      Q.positiveHalfPullback n (Pn.positiveTimeElement F) +
        Q.positiveHalfPullback n (Pn.positiveTimeElement G)
    rw [Pn.positiveTimeElement_add]
    exact (Q.positiveHalfPullback n).map_add _ _
  map_smul := by
    intro n r F
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    change Q.positiveHalfPullback n (Pn.positiveTimeElement (r • F)) =
      r • Q.positiveHalfPullback n (Pn.positiveTimeElement F)
    rw [Pn.positiveTimeElement_smul]
    exact (Q.positiveHalfPullback n).map_smul r _

/-- The coherent bridge therefore gives a canonical linear-isometric boundary
realization of every approximating OS carrier. -/
noncomputable def boundaryMomentLinearIsometry
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ) :
    (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier →ₗᵢ[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N :=
  (Q.toPositiveHalfPullbackLinearCoherence hInvariant).boundaryMomentLinearIsometry n

@[simp] theorem boundaryMomentLinearIsometry_apply
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    Q.boundaryMomentLinearIsometry hInvariant n F =
      physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F :=
  rfl

/-- The coherent positive-time pullback as an open-half Haar `L²` linear map on
the actual OS carrier. -/
noncomputable def positiveHalfL2LinearMap
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ) :
    (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier →ₗ[ℝ]
      PhysicalYangMillsEvenPeriodicWilsonOSOpenHalfFeatureL2 halfExtent N n :=
  (Q.toPositiveHalfPullbackLinearCoherence hInvariant).positiveHalfObservableL2LinearMap n

@[simp] theorem positiveHalfL2LinearMap_apply
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    Q.positiveHalfL2LinearMap hInvariant n F =
      physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservableL2
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F :=
  rfl

/-- Canonical time-dependent positive-half analysis on the *OS carrier*.

This is the first actual construction of the time-dependent analysis factor:
translate the physical positive-time observable by half the Euclidean time and
then apply the coherent finite-Wilson positive-half pullback.  It is a genuine
real linear map without any additional intertwining hypothesis. -/
noncomputable def translatedPositiveHalfL2LinearMap
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
    (n : ℕ) (t : NNReal) :
    (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier →ₗ[ℝ]
      PhysicalYangMillsEvenPeriodicWilsonOSOpenHalfFeatureL2 halfExtent N n :=
  (Q.positiveHalfL2LinearMap hInvariant n).comp
    ((C.toPositiveTimeObservableContractionSemigroup n).carrierTranslation (t / 2))

@[simp] theorem translatedPositiveHalfL2LinearMap_apply
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
    Q.translatedPositiveHalfL2LinearMap hInvariant C n t F =
      physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservableL2
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
        ((C.toPositiveTimeObservableContractionSemigroup n).carrierTranslation
          (t / 2) F) := by
  rfl

/-- Exact carrier-level factorization/intertwining identity.

For the actually constructed time-dependent positive-half analysis `U_{n,t}`,
actual Wilson adjoint synthesis gives exactly the boundary realization of the
half-time translated OS carrier:

`A_φ† (U_{n,t} F) = J_n (T_n(t/2) F)`.

Hence the abstract intertwining field in the boundary-transfer certificate is
already theorem-generated on the dense OS carrier once a coherent finite
positive-time pullback is supplied. -/
theorem actualSynthesis_translatedPositiveHalfL2LinearMap_apply
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
      Q.boundaryMomentLinearIsometry hInvariant n
        ((C.toPositiveTimeObservableContractionSemigroup n).carrierTranslation
          (t / 2) F) := by
  rw [Q.translatedPositiveHalfL2LinearMap_apply,
    Q.boundaryMomentLinearIsometry_apply]
  exact
    (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2_eq_actualSynthesis
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
      ((C.toPositiveTimeObservableContractionSemigroup n).carrierTranslation
        (t / 2) F)).symm

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end MathlibAnalytic
end MGAP4D

end