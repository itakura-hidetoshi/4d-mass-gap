import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSActualLinearHalfSupportReflection
import Mathlib.Topology.ContinuousMap.Bounded.Basic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance actualCanonicalPositiveHalfSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance actualCanonicalPositiveHalfSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance actualCanonicalPositiveHalfSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance actualCanonicalPositiveHalfSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance actualCanonicalPositiveHalfSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance actualCanonicalPositiveHalfSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- A canonical full-lattice extension of one positive open-half configuration.
The reflection-fixed boundary and the negative open half are filled with the
identity.  Its positive restriction is exactly the original open-half point. -/
def periodicHypercubicEvenSpecialUnitaryPositiveHalfSection
    (H N : ℕ)
    (x : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) :
    PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ :=
  (periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
    (fun _ => 1) x (fun _ => 1)

@[simp] theorem periodicHypercubicEvenSpecialUnitaryPositiveRestriction_positiveHalfSection
    (H N : ℕ)
    (x : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) :
    (periodicHypercubicEvenEdgeOrbitPartition H).positiveRestriction
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfSection H N x) = x := by
  exact
    (periodicHypercubicEvenEdgeOrbitPartition H)
      |>.positiveRestriction_boundaryFiberedAssemble (fun _ => 1) x (fun _ => 1)

/-- Evaluate a physical gauge-invariant observable on the canonical extension
of a positive open-half lattice configuration. -/
def physicalYangMillsEvenPeriodicWilsonOSCanonicalHalfSectionEvaluation
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (interpolate :
      ∀ n,
        (PeriodicHypercubicEvenEdge (halfExtent n) →
          Matrix.specialUnitaryGroup (Fin N) ℂ) → S.Configuration)
    (n : ℕ)
    (O : physicalYangMillsGaugeInvariantObservableSubalgebra S)
    (x : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
      (halfExtent n) N) : ℝ :=
  ((O : BoundedContinuousFunction S.Configuration ℝ)
    (interpolate n
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfSection
        (halfExtent n) N x)))

/-- First-order positive-time support expressed intrinsically through the
canonical positive-half section.

At every scale the section evaluation must be continuous, and the original
observable pullback must be constant on every fiber of `positiveRestriction`.
No positive-half representative is chosen: its value is forced by the
canonical section. -/
def PhysicalYangMillsEvenPeriodicWilsonOSIsCanonicalPositiveTime
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (interpolate :
      ∀ n,
        (PeriodicHypercubicEvenEdge (halfExtent n) →
          Matrix.specialUnitaryGroup (Fin N) ℂ) → S.Configuration)
    (O : physicalYangMillsGaugeInvariantObservableSubalgebra S) : Prop :=
  ∀ n,
    Continuous
        (physicalYangMillsEvenPeriodicWilsonOSCanonicalHalfSectionEvaluation
          S halfExtent N interpolate n O) ∧
      ∀ A : PeriodicHypercubicEvenEdge (halfExtent n) →
          Matrix.specialUnitaryGroup (Fin N) ℂ,
        ((O : BoundedContinuousFunction S.Configuration ℝ) (interpolate n A)) =
          physicalYangMillsEvenPeriodicWilsonOSCanonicalHalfSectionEvaluation
            S halfExtent N interpolate n O
            ((periodicHypercubicEvenEdgeOrbitPartition (halfExtent n)).positiveRestriction A)

/-- The gauge-invariant bounded continuous observables whose finite-lattice
pullbacks depend only on the positive open half at every scale form a real
subalgebra.  This constructs the positive-time observable algebra rather than
assuming it as an opaque field. -/
def physicalYangMillsEvenPeriodicWilsonOSCanonicalPositiveTimeSubalgebra
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (interpolate :
      ∀ n,
        (PeriodicHypercubicEvenEdge (halfExtent n) →
          Matrix.specialUnitaryGroup (Fin N) ℂ) → S.Configuration) :
    Subalgebra ℝ (physicalYangMillsGaugeInvariantObservableSubalgebra S) where
  carrier :=
    {O | PhysicalYangMillsEvenPeriodicWilsonOSIsCanonicalPositiveTime
      S halfExtent N interpolate O}
  mul_mem' := by
    intro O₁ O₂ h₁ h₂ n
    constructor
    · simpa [physicalYangMillsEvenPeriodicWilsonOSCanonicalHalfSectionEvaluation] using
        (h₁ n).1.mul (h₂ n).1
    · intro A
      have hO₁ := (h₁ n).2 A
      have hO₂ := (h₂ n).2 A
      simpa [physicalYangMillsEvenPeriodicWilsonOSCanonicalHalfSectionEvaluation] using
        congrArg₂ (fun a b : ℝ => a * b) hO₁ hO₂
  add_mem' := by
    intro O₁ O₂ h₁ h₂ n
    constructor
    · simpa [physicalYangMillsEvenPeriodicWilsonOSCanonicalHalfSectionEvaluation] using
        (h₁ n).1.add (h₂ n).1
    · intro A
      have hO₁ := (h₁ n).2 A
      have hO₂ := (h₂ n).2 A
      simpa [physicalYangMillsEvenPeriodicWilsonOSCanonicalHalfSectionEvaluation] using
        congrArg₂ (fun a b : ℝ => a + b) hO₁ hO₂
  algebraMap_mem' := by
    intro r n
    constructor
    · simpa [physicalYangMillsEvenPeriodicWilsonOSCanonicalHalfSectionEvaluation] using
        (continuous_const : Continuous
          (fun _ : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
            (halfExtent n) N => r))
    · intro A
      simp [physicalYangMillsEvenPeriodicWilsonOSCanonicalHalfSectionEvaluation]

@[simp] theorem mem_physicalYangMillsEvenPeriodicWilsonOSCanonicalPositiveTimeSubalgebra_iff
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (interpolate :
      ∀ n,
        (PeriodicHypercubicEvenEdge (halfExtent n) →
          Matrix.specialUnitaryGroup (Fin N) ℂ) → S.Configuration)
    (O : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
    O ∈ physicalYangMillsEvenPeriodicWilsonOSCanonicalPositiveTimeSubalgebra
        S halfExtent N interpolate ↔
      PhysicalYangMillsEvenPeriodicWilsonOSIsCanonicalPositiveTime
        S halfExtent N interpolate O :=
  Iff.rfl

/-- The canonical positive-half bounded continuous representative of an element
of the constructed positive-time algebra.  Compactness of the finite product
of `SU(N)` turns the membership continuity receipt into a bounded continuous
function automatically. -/
noncomputable def physicalYangMillsEvenPeriodicWilsonOSCanonicalPositiveHalfObservable
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (interpolate :
      ∀ n,
        (PeriodicHypercubicEvenEdge (halfExtent n) →
          Matrix.specialUnitaryGroup (Fin N) ℂ) → S.Configuration)
    (n : ℕ)
    (F : (physicalYangMillsEvenPeriodicWilsonOSCanonicalPositiveTimeSubalgebra
      S halfExtent N interpolate).toSubmodule) :
    BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
        (halfExtent n) N) ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨physicalYangMillsEvenPeriodicWilsonOSCanonicalHalfSectionEvaluation
        S halfExtent N interpolate n F.1,
      (F.2 n).1⟩

@[simp] theorem physicalYangMillsEvenPeriodicWilsonOSCanonicalPositiveHalfObservable_apply
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (interpolate :
      ∀ n,
        (PeriodicHypercubicEvenEdge (halfExtent n) →
          Matrix.specialUnitaryGroup (Fin N) ℂ) → S.Configuration)
    (n : ℕ)
    (F : (physicalYangMillsEvenPeriodicWilsonOSCanonicalPositiveTimeSubalgebra
      S halfExtent N interpolate).toSubmodule)
    (x : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
      (halfExtent n) N) :
    physicalYangMillsEvenPeriodicWilsonOSCanonicalPositiveHalfObservable
        S halfExtent N interpolate n F x =
      physicalYangMillsEvenPeriodicWilsonOSCanonicalHalfSectionEvaluation
        S halfExtent N interpolate n F.1 x :=
  rfl

/-- Canonical section evaluation is real-linear in the physical observable, so
the constructed positive-time algebra carries a canonical positive-half
bounded-continuous linear pullback. -/
noncomputable def physicalYangMillsEvenPeriodicWilsonOSCanonicalPositiveHalfLinearMap
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (interpolate :
      ∀ n,
        (PeriodicHypercubicEvenEdge (halfExtent n) →
          Matrix.specialUnitaryGroup (Fin N) ℂ) → S.Configuration)
    (n : ℕ) :
    (physicalYangMillsEvenPeriodicWilsonOSCanonicalPositiveTimeSubalgebra
      S halfExtent N interpolate).toSubmodule →ₗ[ℝ]
      BoundedContinuousFunction
        (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
          (halfExtent n) N) ℝ where
  toFun :=
    physicalYangMillsEvenPeriodicWilsonOSCanonicalPositiveHalfObservable
      S halfExtent N interpolate n
  map_add' := by
    intro F G
    ext x
    rfl
  map_smul' := by
    intro r F
    ext x
    rfl

/-- Membership in the constructed positive-time algebra theorem-generates the
first-order half-support identity required by PR #2049. -/
theorem physicalYangMillsEvenPeriodicWilsonOSCanonicalPositiveHalfLinearMap_pullback
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (interpolate :
      ∀ n,
        (PeriodicHypercubicEvenEdge (halfExtent n) →
          Matrix.specialUnitaryGroup (Fin N) ℂ) → S.Configuration)
    (n : ℕ)
    (F : (physicalYangMillsEvenPeriodicWilsonOSCanonicalPositiveTimeSubalgebra
      S halfExtent N interpolate).toSubmodule)
    (A : PeriodicHypercubicEvenEdge (halfExtent n) →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    ((F.1 : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
        BoundedContinuousFunction S.Configuration ℝ) (interpolate n A) =
      physicalYangMillsEvenPeriodicWilsonOSCanonicalPositiveHalfLinearMap
        S halfExtent N interpolate n F
        ((periodicHypercubicEvenEdgeOrbitPartition (halfExtent n)).positiveRestriction A) := by
  exact (F.2 n).2 A

/-- Model data still needed after the positive-time observable algebra and its
linear positive-half pullback have been constructed canonically.

Only the physical configuration reflection and its compatibility with the
chosen lattice interpolation remain here, together with the already-existing
pushforward identification of the approximating Wilson law. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n) where
  interpolate :
    ∀ n,
      (PeriodicHypercubicEvenEdge (halfExtent n) →
        Matrix.specialUnitaryGroup (Fin N) ℂ) → S.Configuration
  interpolate_measurable : ∀ n, Measurable (interpolate n)
  approximatingMeasure_toMeasure_eq :
    ∀ n,
      (S.approximatingMeasure n : Measure S.Configuration) =
        Measure.map (interpolate n)
          (periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength (halfExtent n))
            N hN (beta n) (hbeta n)).gibbsMeasure
  configurationReflection : Homeomorph S.Configuration S.Configuration
  reflection_gauge_commute : ∀ g X,
    configurationReflection (S.action g X) =
      S.action g (configurationReflection X)
  configurationReflection_involutive : Function.Involutive configurationReflection
  interpolate_reflection :
    ∀ n A,
      configurationReflection (interpolate n A) =
        interpolate n
          (periodicHypercubicEvenConfigurationReflection (halfExtent n) A)

namespace PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}

/-- The canonical positive-time fiber algebra together with a physical
configuration reflection gives an actual OS reflection datum. -/
noncomputable def reflectionData
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection
      S halfExtent N hN beta hbeta) :
    PhysicalYangMillsGaugeInvariantOSReflectionData S where
  positiveTimeSubalgebra :=
    physicalYangMillsEvenPeriodicWilsonOSCanonicalPositiveTimeSubalgebra
      S halfExtent N R.interpolate
  reflection :=
    (physicalGaugeInvariantObservablePrecompAlgEquiv
      S R.configurationReflection R.reflection_gauge_commute).toAlgHom
  reflection_involutive := by
    intro O
    apply Subtype.ext
    ext X
    change
      ((O : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
        BoundedContinuousFunction S.Configuration ℝ)
          (R.configurationReflection (R.configurationReflection X)) =
        ((O : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
          BoundedContinuousFunction S.Configuration ℝ) X
    rw [R.configurationReflection_involutive X]

/-- The canonical fiber positive-time algebra removes the first-order
`observable_pullback` assumption from PR #2049: it follows directly from
subalgebra membership. -/
noncomputable def toLinearHalfSupportReflection
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection
      S halfExtent N hN beta hbeta) :
    PhysicalYangMillsEvenPeriodicWilsonOSLinearHalfSupportReflection
      S R.reflectionData halfExtent N hN beta hbeta where
  interpolate := R.interpolate
  interpolate_measurable := R.interpolate_measurable
  positiveHalfPullback :=
    physicalYangMillsEvenPeriodicWilsonOSCanonicalPositiveHalfLinearMap
      S halfExtent N R.interpolate
  approximatingMeasure_toMeasure_eq := R.approximatingMeasure_toMeasure_eq
  configurationReflection := R.configurationReflection
  reflection_gauge_commute := R.reflection_gauge_commute
  reflection_realization := by
    intro O
    rfl
  interpolate_reflection := R.interpolate_reflection
  observable_pullback := by
    intro n F A
    exact
      physicalYangMillsEvenPeriodicWilsonOSCanonicalPositiveHalfLinearMap_pullback
        S halfExtent N R.interpolate n ⟨F.1, F.2⟩ A

/-- Therefore the canonical positive-time fiber algebra plus reflection
covariance already generate the complete separated actual Wilson boundary
representation. -/
noncomputable def toSeparatedBoundaryMomentLinearIsometry
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection
      S halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      R.reflectionData.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ) :
    (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S R.reflectionData halfExtent N hN beta hbeta
        R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
        hInvariant n).Separated →ₗᵢ[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N :=
  R.toLinearHalfSupportReflection.toSeparatedBoundaryMomentLinearIsometry
    hInvariant n

end PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection

end

end MathlibAnalytic
end MGAP4D
