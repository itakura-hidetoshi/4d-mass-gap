import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2NormalizedTracePowerTietzeReadout
import MGAP4D.MathlibAnalytic.PhysicalYangMillsDenseInterpolationCrossScaleReadout
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Topology
open scoped ENNReal InnerProduct InnerProductSpace

noncomputable section

private theorem normalizedTracePowerCrossScaleTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

namespace PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}

private abbrev normalizedTracePowerCrossScaleFullConfiguration
    (halfExtent : ℕ → ℕ) (n : ℕ) :=
  PeriodicHypercubicEvenEdge (halfExtent n) →
    Matrix.specialUnitaryGroup (Fin 2) ℂ

/-- The union of the actual finite SU(2) Wilson interpolation images over all
scales.  This is the natural carrier on which a scale-independent physical
readout is prescribed before any continuum extension is invoked. -/
def normalizedTracePowerInterpolationImageUnion
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 normalizedTracePowerCrossScaleTwoRankPositive beta hbeta) :
    Set S.Configuration :=
  {X | ∃ (n : ℕ)
      (A : normalizedTracePowerCrossScaleFullConfiguration halfExtent n),
      Q.interpolate n A = X}

/-- Exact compatibility condition for normalized-trace-power readout across
finite Wilson scales: whenever two finite configurations represent the same
physical configuration, their prescribed readout values coincide. -/
def normalizedTracePowerCrossScaleCompatible
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 normalizedTracePowerCrossScaleTwoRankPositive beta hbeta)
    (j : ℕ) : Prop :=
  ∀ (n m : ℕ)
    (A : normalizedTracePowerCrossScaleFullConfiguration halfExtent n)
    (B : normalizedTracePowerCrossScaleFullConfiguration halfExtent m),
    Q.interpolate n A = Q.interpolate m B →
      normalizedTracePowerTietzeFullTarget halfExtent beta hbeta n j A =
        normalizedTracePowerTietzeFullTarget halfExtent beta hbeta m j B

/-- A genuine cross-scale continuum realization of one normalized trace power.
Unlike the per-scale Tietze theorem, this contains one and the same bounded
continuous physical observable for every lattice scale. -/
structure PhysicalYangMillsWilsonSU2NormalizedTracePowerCrossScaleExtension
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 normalizedTracePowerCrossScaleTwoRankPositive beta hbeta)
    (j : ℕ) where
  observable : BoundedContinuousFunction S.Configuration ℝ
  readout : ∀ (n : ℕ)
    (A : normalizedTracePowerCrossScaleFullConfiguration halfExtent n),
    observable (Q.interpolate n A) =
      normalizedTracePowerTietzeFullTarget halfExtent beta hbeta n j A

namespace PhysicalYangMillsWilsonSU2NormalizedTracePowerCrossScaleExtension

variable
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 normalizedTracePowerCrossScaleTwoRankPositive beta hbeta}
    {j : ℕ}

/-- Existence of one physical observable across all scales forces the exact
same-root compatibility condition. -/
theorem compatible
    (R : PhysicalYangMillsWilsonSU2NormalizedTracePowerCrossScaleExtension Q j) :
    normalizedTracePowerCrossScaleCompatible Q j := by
  intro n m A B hAB
  calc
    normalizedTracePowerTietzeFullTarget halfExtent beta hbeta n j A =
        R.observable (Q.interpolate n A) := (R.readout n A).symm
    _ = R.observable (Q.interpolate m B) := congrArg (fun X => R.observable X) hAB
    _ = normalizedTracePowerTietzeFullTarget halfExtent beta hbeta m j B :=
      R.readout m B

/-- Consequently, failure of cross-scale compatibility is a formal obstruction
to any single bounded-continuous continuum realization. -/
theorem not_nonempty_of_not_compatible
    (h : ¬ normalizedTracePowerCrossScaleCompatible Q j) :
    ¬ Nonempty
      (PhysicalYangMillsWilsonSU2NormalizedTracePowerCrossScaleExtension Q j) := by
  intro hR
  rcases hR with ⟨R⟩
  exact h R.compatible

/-- On a dense union of actual finite Wilson interpolation images, a prescribed
cross-scale normalized-trace-power extension is unique.  Hence the remaining
model-facing problem is existence, not ambiguity. -/
theorem observable_unique_of_dense_interpolation
    (hDense : Dense (normalizedTracePowerInterpolationImageUnion Q))
    (R₁ R₂ :
      PhysicalYangMillsWilsonSU2NormalizedTracePowerCrossScaleExtension Q j) :
    R₁.observable = R₂.observable := by
  have hfun :
      (fun X : S.Configuration => R₁.observable X) =
        (fun X : S.Configuration => R₂.observable X) := by
    apply Continuous.ext_on hDense
    · exact R₁.observable.continuous
    · exact R₂.observable.continuous
    · intro X hX
      rcases hX with ⟨n, A, rfl⟩
      change R₁.observable (Q.interpolate n A) =
        R₂.observable (Q.interpolate n A)
      calc
        R₁.observable (Q.interpolate n A) =
            normalizedTracePowerTietzeFullTarget halfExtent beta hbeta n j A :=
          R₁.readout n A
        _ = R₂.observable (Q.interpolate n A) := (R₂.readout n A).symm
  ext X
  exact congrFun hfun X

/-- A global cross-scale extension agrees on every finite image with any
per-scale extension carrying the same exact Tietze target. -/
theorem agrees_with_perScaleExtension_on_interpolation
    (R : PhysicalYangMillsWilsonSU2NormalizedTracePowerCrossScaleExtension Q j)
    (n : ℕ)
    (O : BoundedContinuousFunction S.Configuration ℝ)
    (hO : ∀ A : normalizedTracePowerCrossScaleFullConfiguration halfExtent n,
      O (Q.interpolate n A) =
        normalizedTracePowerTietzeFullTarget halfExtent beta hbeta n j A)
    (A : normalizedTracePowerCrossScaleFullConfiguration halfExtent n) :
    R.observable (Q.interpolate n A) = O (Q.interpolate n A) := by
  calc
    R.observable (Q.interpolate n A) =
        normalizedTracePowerTietzeFullTarget halfExtent beta hbeta n j A :=
      R.readout n A
    _ = O (Q.interpolate n A) := (hO A).symm

end PhysicalYangMillsWilsonSU2NormalizedTracePowerCrossScaleExtension

/-- Countable cross-scale realization of all normalized trace powers by one
physical observable per power, uniformly across every finite Wilson scale. -/
structure PhysicalYangMillsWilsonSU2NormalizedTracePowerCrossScaleFamily
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 normalizedTracePowerCrossScaleTwoRankPositive beta hbeta) where
  observable : ℕ → BoundedContinuousFunction S.Configuration ℝ
  readout : ∀ (j n : ℕ)
    (A : normalizedTracePowerCrossScaleFullConfiguration halfExtent n),
    observable j (Q.interpolate n A) =
      normalizedTracePowerTietzeFullTarget halfExtent beta hbeta n j A

namespace PhysicalYangMillsWilsonSU2NormalizedTracePowerCrossScaleFamily

variable
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 normalizedTracePowerCrossScaleTwoRankPositive beta hbeta}

/-- Select one normalized trace power from a scale-coherent family. -/
noncomputable def select
    (R : PhysicalYangMillsWilsonSU2NormalizedTracePowerCrossScaleFamily Q)
    (j : ℕ) :
    PhysicalYangMillsWilsonSU2NormalizedTracePowerCrossScaleExtension Q j where
  observable := R.observable j
  readout := R.readout j

/-- Every member of a genuine cross-scale family satisfies the necessary
same-root compatibility condition. -/
theorem compatible
    (R : PhysicalYangMillsWilsonSU2NormalizedTracePowerCrossScaleFamily Q)
    (j : ℕ) :
    normalizedTracePowerCrossScaleCompatible Q j :=
  (R.select j).compatible

/-- If the actual interpolation union is dense, the physical observable at each
trace power is uniquely determined by its finite Wilson readouts. -/
theorem observable_unique_of_dense_interpolation
    (hDense : Dense (normalizedTracePowerInterpolationImageUnion Q))
    (R₁ R₂ : PhysicalYangMillsWilsonSU2NormalizedTracePowerCrossScaleFamily Q)
    (j : ℕ) :
    R₁.observable j = R₂.observable j :=
  (R₁.select j).observable_unique_of_dense_interpolation hDense (R₂.select j)

end PhysicalYangMillsWilsonSU2NormalizedTracePowerCrossScaleFamily

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end

end MathlibAnalytic
end MGAP4D
