import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2PositiveHalfCylinderReadout
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Set Topology
open scoped ENNReal InnerProduct InnerProductSpace

noncomputable section

private theorem positiveHalfCylinderReadableTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance positiveHalfCylinderReadableNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance positiveHalfCylinderReadableTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance positiveHalfCylinderReadableCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance positiveHalfCylinderReadableSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance positiveHalfCylinderReadableMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance positiveHalfCylinderReadableBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance positiveHalfCylinderReadableSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

namespace PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}

private abbrev PositiveHalfCylinderTarget
    (halfExtent : ℕ → ℕ) (n : ℕ) :=
  BoundedContinuousFunction
    (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
      (halfExtent n) 2) ℝ

namespace PhysicalYangMillsWilsonSU2PositiveHalfCylinderReadout

variable
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 positiveHalfCylinderReadableTwoRankPositive beta hbeta}
    {n : ℕ}
    {f g : PositiveHalfCylinderTarget halfExtent n}

/-- Readable positive-half cylinder targets are closed under pointwise addition
because the corresponding physical observables can be added inside the given
positive-time subalgebra.  No algebraic property of `positiveHalfPullback` is
used here. -/
protected def add
    (Rf : PhysicalYangMillsWilsonSU2PositiveHalfCylinderReadout Q n f)
    (Rg : PhysicalYangMillsWilsonSU2PositiveHalfCylinderReadout Q n g) :
    PhysicalYangMillsWilsonSU2PositiveHalfCylinderReadout Q n (f + g) where
  observable := Rf.observable + Rg.observable
  positive := by
    intro A
    change
      (((Rf.observable : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
          BoundedContinuousFunction S.Configuration ℝ) (Q.interpolate n A) +
        ((Rg.observable : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
          BoundedContinuousFunction S.Configuration ℝ) (Q.interpolate n A)) =
      f ((periodicHypercubicEvenEdgeOrbitPartition
          (halfExtent n)).positiveRestriction A) +
        g ((periodicHypercubicEvenEdgeOrbitPartition
          (halfExtent n)).positiveRestriction A)
    rw [Rf.positive A, Rg.positive A]

/-- Readable positive-half cylinder targets are closed under pointwise
multiplication because `D.positiveTimeSubalgebra` is already a subalgebra. -/
protected def mul
    (Rf : PhysicalYangMillsWilsonSU2PositiveHalfCylinderReadout Q n f)
    (Rg : PhysicalYangMillsWilsonSU2PositiveHalfCylinderReadout Q n g) :
    PhysicalYangMillsWilsonSU2PositiveHalfCylinderReadout Q n (f * g) where
  observable := Rf.observable * Rg.observable
  positive := by
    intro A
    change
      (((Rf.observable : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
          BoundedContinuousFunction S.Configuration ℝ) (Q.interpolate n A) *
        ((Rg.observable : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
          BoundedContinuousFunction S.Configuration ℝ) (Q.interpolate n A)) =
      f ((periodicHypercubicEvenEdgeOrbitPartition
          (halfExtent n)).positiveRestriction A) *
        g ((periodicHypercubicEvenEdgeOrbitPartition
          (halfExtent n)).positiveRestriction A)
    rw [Rf.positive A, Rg.positive A]

/-- Every real constant target is readable by the corresponding scalar
observable in the positive-time subalgebra. -/
protected def ofReal
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 positiveHalfCylinderReadableTwoRankPositive beta hbeta)
    (n : ℕ)
    (r : ℝ) :
    PhysicalYangMillsWilsonSU2PositiveHalfCylinderReadout Q n
      (algebraMap ℝ (PositiveHalfCylinderTarget halfExtent n) r) where
  observable := algebraMap ℝ D.positiveTimeSubalgebra r
  positive := by
    intro A
    change r = r
    rfl

end PhysicalYangMillsWilsonSU2PositiveHalfCylinderReadout

/-- The bounded-continuous positive-half targets admitting a genuine physical
positive-time cylinder readout form a real subalgebra.

The algebra structure is inherited from the physical positive-time observable
subalgebra at the witness level.  In particular this definition does not assume
that the coherent linear pullback is multiplicative. -/
def positiveHalfCylinderReadableSubalgebra
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 positiveHalfCylinderReadableTwoRankPositive beta hbeta)
    (n : ℕ) :
    Subalgebra ℝ (PositiveHalfCylinderTarget halfExtent n) where
  carrier := {f |
    Nonempty (PhysicalYangMillsWilsonSU2PositiveHalfCylinderReadout Q n f)}
  mul_mem' := by
    intro f g hf hg
    rcases hf with ⟨Rf⟩
    rcases hg with ⟨Rg⟩
    exact ⟨Rf.mul Rg⟩
  add_mem' := by
    intro f g hf hg
    rcases hf with ⟨Rf⟩
    rcases hg with ⟨Rg⟩
    exact ⟨Rf.add Rg⟩
  algebraMap_mem' := by
    intro r
    exact ⟨PhysicalYangMillsWilsonSU2PositiveHalfCylinderReadout.ofReal Q n r⟩

@[simp]
theorem mem_positiveHalfCylinderReadableSubalgebra_iff
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 positiveHalfCylinderReadableTwoRankPositive beta hbeta)
    (n : ℕ)
    (f : PositiveHalfCylinderTarget halfExtent n) :
    f ∈ positiveHalfCylinderReadableSubalgebra Q n ↔
      Nonempty (PhysicalYangMillsWilsonSU2PositiveHalfCylinderReadout Q n f) :=
  Iff.rfl

/-- Once the already-proved reflection and vacuum-unit compatibilities are
available, every readable target belongs to the exact coherent positive-half
pullback range. -/
theorem positiveHalfCylinderReadableSubalgebra_subset_positiveHalfPullbackRange
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 positiveHalfCylinderReadableTwoRankPositive beta hbeta)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSInterpolationReflectionCompatibility Q)
    (hInvariant : ∀ m,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S m))
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant)
    (n : ℕ) :
    (↑(positiveHalfCylinderReadableSubalgebra Q n) :
      Set (PositiveHalfCylinderTarget halfExtent n)) ⊆
      LinearMap.range (Q.positiveHalfPullback n) := by
  intro f hf
  change Nonempty
    (PhysicalYangMillsWilsonSU2PositiveHalfCylinderReadout Q n f) at hf
  rcases hf with ⟨R⟩
  exact
    Q.positiveHalfCylinderReadout_mem_positiveHalfPullbackRange
      C hInvariant U n f R

/-- Consequently the sup-norm closure of the readable target algebra lies in
the closure of the coherent positive-half pullback range. -/
theorem closure_positiveHalfCylinderReadableSubalgebra_subset_positiveHalfPullbackRangeClosure
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 positiveHalfCylinderReadableTwoRankPositive beta hbeta)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSInterpolationReflectionCompatibility Q)
    (hInvariant : ∀ m,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S m))
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant)
    (n : ℕ) :
    closure (↑(positiveHalfCylinderReadableSubalgebra Q n) :
      Set (PositiveHalfCylinderTarget halfExtent n)) ⊆
      closure (LinearMap.range (Q.positiveHalfPullback n)) :=
  closure_mono
    (Q.positiveHalfCylinderReadableSubalgebra_subset_positiveHalfPullbackRange
      C hInvariant U n)

/-- A family of readable generators generates only readable polynomial targets.
This is the algebraic handoff needed before any density or Stone--Weierstrass
argument: generator realization is enough; no whole-algebra lift is primitive. -/
theorem algebraAdjoin_le_positiveHalfCylinderReadableSubalgebra
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 positiveHalfCylinderReadableTwoRankPositive beta hbeta)
    (n : ℕ)
    (s : Set (PositiveHalfCylinderTarget halfExtent n))
    (hs : s ⊆ (↑(positiveHalfCylinderReadableSubalgebra Q n) :
      Set (PositiveHalfCylinderTarget halfExtent n))) :
    Algebra.adjoin ℝ s ≤ positiveHalfCylinderReadableSubalgebra Q n := by
  exact Algebra.adjoin_le.2 hs

/-- Therefore a uniform limit of polynomials generated by readable cylinders is
already in the coherent positive-half pullback range closure. -/
theorem closure_algebraAdjoin_subset_positiveHalfPullbackRangeClosure
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 positiveHalfCylinderReadableTwoRankPositive beta hbeta)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSInterpolationReflectionCompatibility Q)
    (hInvariant : ∀ m,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S m))
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant)
    (n : ℕ)
    (s : Set (PositiveHalfCylinderTarget halfExtent n))
    (hs : s ⊆ (↑(positiveHalfCylinderReadableSubalgebra Q n) :
      Set (PositiveHalfCylinderTarget halfExtent n))) :
    closure (↑(Algebra.adjoin ℝ s) :
      Set (PositiveHalfCylinderTarget halfExtent n)) ⊆
      closure (LinearMap.range (Q.positiveHalfPullback n)) := by
  apply closure_mono
  intro f hf
  exact
    Q.positiveHalfCylinderReadableSubalgebra_subset_positiveHalfPullbackRange
      C hInvariant U n
      ((Q.algebraAdjoin_le_positiveHalfCylinderReadableSubalgebra n s hs) hf)

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end

end MathlibAnalytic
end MGAP4D
