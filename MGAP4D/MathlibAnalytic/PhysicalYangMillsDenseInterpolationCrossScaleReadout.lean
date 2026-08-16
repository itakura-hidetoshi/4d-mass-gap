import MGAP4D.MathlibAnalytic.PhysicalYangMillsDenseInterpolationGaugeInvariantObservable

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Topology

noncomputable section

namespace ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.PhysicalGaugeAction

variable {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}

/-- A finite readout family is cross-scale compatible when any two finite
configurations that interpolate to the same physical configuration have the
same readout value.  This is the exact compatibility forced by the existence
of one continuum observable reading every Wilson scale simultaneously. -/
def interpolationReadoutCompatible
    (G : E.PhysicalGaugeAction)
    (target : (n : ℕ) → (E.system n).base.Configuration → ℝ) : Prop :=
  ∀ (n m : ℕ)
    (U : (E.system n).base.Configuration)
    (V : (E.system m).base.Configuration),
    E.interpolate n U = E.interpolate m V →
      target n U = target m V

/-- Any single bounded-continuous physical observable with exact same-root
readout at every scale automatically forces cross-scale compatibility. -/
theorem interpolationReadoutCompatible_of_boundedContinuous_readout
    (G : E.PhysicalGaugeAction)
    (O : BoundedContinuousFunction E.PhysicalConfiguration ℝ)
    (target : (n : ℕ) → (E.system n).base.Configuration → ℝ)
    (hreadout : ∀ (n : ℕ) (U : (E.system n).base.Configuration),
      O (E.interpolate n U) = target n U) :
    G.interpolationReadoutCompatible target := by
  intro n m U V hUV
  calc
    target n U = O (E.interpolate n U) := (hreadout n U).symm
    _ = O (E.interpolate m V) := congrArg (fun X => O X) hUV
    _ = target m V := hreadout m V

/-- The remaining global-extension datum after the finite Wilson geometry has
been fixed: one bounded-continuous physical observable whose restrictions to
all finite interpolation images are the prescribed targets. -/
structure DenseInterpolationTargetExtension
    (G : E.PhysicalGaugeAction)
    (target : (n : ℕ) → (E.system n).base.Configuration → ℝ) where
  observable : BoundedContinuousFunction E.PhysicalConfiguration ℝ
  readout : ∀ (n : ℕ) (U : (E.system n).base.Configuration),
    observable (E.interpolate n U) = target n U

namespace DenseInterpolationTargetExtension

variable
    {G : E.PhysicalGaugeAction}
    {target : (n : ℕ) → (E.system n).base.Configuration → ℝ}

/-- Cross-scale compatibility is not an extra assumption once a genuine global
extension exists; it is theorem-generated from exact readout. -/
theorem compatible
    (R : DenseInterpolationTargetExtension G target) :
    G.interpolationReadoutCompatible target :=
  G.interpolationReadoutCompatible_of_boundedContinuous_readout
    R.observable target R.readout

/-- On a dense union of interpolation images, a prescribed exact finite readout
has at most one bounded-continuous physical extension.  Thus the unresolved
model-facing issue is existence, not ambiguity of the continuum observable. -/
theorem observable_unique_of_dense_interpolation
    (hDense : Dense G.interpolationImageUnion)
    (R₁ R₂ : DenseInterpolationTargetExtension G target) :
    R₁.observable = R₂.observable := by
  have hfun :
      (fun X : E.PhysicalConfiguration => R₁.observable X) =
        (fun X : E.PhysicalConfiguration => R₂.observable X) := by
    apply Continuous.ext_on hDense
    · exact R₁.observable.continuous
    · exact R₂.observable.continuous
    · intro X hX
      rcases hX with ⟨n, U, rfl⟩
      change R₁.observable (E.interpolate n U) =
        R₂.observable (E.interpolate n U)
      calc
        R₁.observable (E.interpolate n U) = target n U := R₁.readout n U
        _ = R₂.observable (E.interpolate n U) := (R₂.readout n U).symm
  ext X
  exact congrFun hfun X

/-- Once the global cross-scale extension exists, finite gauge invariance of the
prescribed targets and density of the interpolation union generate the existing
physical gauge-invariant observable.  No Haar averaging or global pullback
surjectivity is used. -/
noncomputable def toGaugeInvariantObservable
    (R : DenseInterpolationTargetExtension G target)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (hDense : Dense G.interpolationImageUnion)
    (htarget : ∀ (n : ℕ) (g : G.Symmetry)
      (U : (E.system n).base.Configuration),
      target n
          ((E.system n).base.gaugeTransform (G.latticeGauge n g) U) =
        target n U) :
    physicalYangMillsGaugeInvariantObservableSubalgebra (G.toSymmetryLimit L) :=
  G.gaugeInvariantObservableOfDenseInterpolationReadout
    L hDense R.observable target R.readout htarget

@[simp] theorem toGaugeInvariantObservable_apply
    (R : DenseInterpolationTargetExtension G target)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (hDense : Dense G.interpolationImageUnion)
    (htarget : ∀ (n : ℕ) (g : G.Symmetry)
      (U : (E.system n).base.Configuration),
      target n
          ((E.system n).base.gaugeTransform (G.latticeGauge n g) U) =
        target n U)
    (X : E.PhysicalConfiguration) :
    ((R.toGaugeInvariantObservable L hDense htarget :
        physicalYangMillsGaugeInvariantObservableSubalgebra
          (G.toSymmetryLimit L)) :
      BoundedContinuousFunction (G.toSymmetryLimit L).Configuration ℝ) X =
      R.observable X :=
  rfl

end DenseInterpolationTargetExtension

/-- Countable target families, such as the normalized-trace powers used by the
actual Wilson excitation route, can be extended scale-coherently by supplying
one physical observable for each target index. -/
structure DenseInterpolationTargetFamilyExtension
    (G : E.PhysicalGaugeAction)
    (target : ℕ → (n : ℕ) → (E.system n).base.Configuration → ℝ) where
  observable : ℕ → BoundedContinuousFunction E.PhysicalConfiguration ℝ
  readout : ∀ (j n : ℕ) (U : (E.system n).base.Configuration),
    observable j (E.interpolate n U) = target j n U

namespace DenseInterpolationTargetFamilyExtension

variable
    {G : E.PhysicalGaugeAction}
    {target : ℕ → (n : ℕ) → (E.system n).base.Configuration → ℝ}

/-- Select one target index from a scale-coherent countable family. -/
noncomputable def select
    (R : DenseInterpolationTargetFamilyExtension G target)
    (j : ℕ) : DenseInterpolationTargetExtension G (target j) where
  observable := R.observable j
  readout := R.readout j

/-- Every member of a genuine global target family is automatically compatible
across Wilson scales. -/
theorem compatible
    (R : DenseInterpolationTargetFamilyExtension G target)
    (j : ℕ) :
    G.interpolationReadoutCompatible (target j) :=
  (R.select j).compatible

/-- Dense interpolation plus finite target gauge invariance turns a whole
countable readout family into physical gauge-invariant observables pointwise. -/
noncomputable def toGaugeInvariantObservable
    (R : DenseInterpolationTargetFamilyExtension G target)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (hDense : Dense G.interpolationImageUnion)
    (htarget : ∀ (j n : ℕ) (g : G.Symmetry)
      (U : (E.system n).base.Configuration),
      target j n
          ((E.system n).base.gaugeTransform (G.latticeGauge n g) U) =
        target j n U)
    (j : ℕ) :
    physicalYangMillsGaugeInvariantObservableSubalgebra (G.toSymmetryLimit L) :=
  (R.select j).toGaugeInvariantObservable L hDense (htarget j)

end DenseInterpolationTargetFamilyExtension

end ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.PhysicalGaugeAction

end

end MathlibAnalytic
end MGAP4D
