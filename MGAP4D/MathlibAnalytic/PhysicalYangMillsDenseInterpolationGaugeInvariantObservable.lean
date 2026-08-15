import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedGaugeSymmetryProkhorovLimit
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantObservableRing
import Mathlib.Topology.Separation.Hausdorff

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Topology

noncomputable section

namespace ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.PhysicalGaugeAction

variable {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}

/-- The union, over all Wilson scales, of the actual finite interpolation
images inside the fixed physical carrier.  Unlike a single finite-scale image,
this set may reasonably be dense in a continuum carrier. -/
def interpolationImageUnion (G : E.PhysicalGaugeAction) :
    Set E.PhysicalConfiguration :=
  {X | ∃ n : ℕ, ∃ U : (E.system n).base.Configuration,
    E.interpolate n U = X}

/-- Global physical gauge invariance of a bounded-continuous observable follows
from gauge invariance of all its finite Wilson pullbacks, provided the union of
actual interpolation images is dense.

The proof uses only the already existing equivariant interpolation and the
Mathlib identity principle for continuous maps on a dense set.  No compact
physical gauge group, Haar averaging, or global surjectivity is required. -/
theorem boundedContinuous_gaugeInvariant_of_dense_interpolation
    (G : E.PhysicalGaugeAction)
    (hDense : Dense G.interpolationImageUnion)
    (O : BoundedContinuousFunction E.PhysicalConfiguration ℝ)
    (hfinite : ∀ (n : ℕ) (g : G.Symmetry)
      (U : (E.system n).base.Configuration),
      O (E.interpolate n
          ((E.system n).base.gaugeTransform (G.latticeGauge n g) U)) =
        O (E.interpolate n U)) :
    ∀ (g : G.Symmetry) (X : E.PhysicalConfiguration),
      O (G.action g X) = O X := by
  intro g X
  have hfun : (fun Y : E.PhysicalConfiguration => O (G.action g Y)) = O := by
    apply Continuous.ext_on hDense
    · exact O.continuous.comp (G.action_continuous g)
    · exact O.continuous
    · intro Y hY
      rcases hY with ⟨n, U, rfl⟩
      rw [← G.interpolate_equivariant n g U]
      exact hfinite n g U
  exact congrFun hfun X

/-- A more model-facing version: if a candidate physical observable has an
exact same-root readout `target n` on every finite interpolation image, and the
finite target family is gauge invariant at every scale, then the physical
observable is globally gauge invariant on a dense interpolation carrier. -/
theorem boundedContinuous_gaugeInvariant_of_dense_interpolation_readout
    (G : E.PhysicalGaugeAction)
    (hDense : Dense G.interpolationImageUnion)
    (O : BoundedContinuousFunction E.PhysicalConfiguration ℝ)
    (target : (n : ℕ) → (E.system n).base.Configuration → ℝ)
    (hreadout : ∀ (n : ℕ) (U : (E.system n).base.Configuration),
      O (E.interpolate n U) = target n U)
    (htarget : ∀ (n : ℕ) (g : G.Symmetry)
      (U : (E.system n).base.Configuration),
      target n
          ((E.system n).base.gaugeTransform (G.latticeGauge n g) U) =
        target n U) :
    ∀ (g : G.Symmetry) (X : E.PhysicalConfiguration),
      O (G.action g X) = O X := by
  apply G.boundedContinuous_gaugeInvariant_of_dense_interpolation hDense O
  intro n g U
  rw [hreadout n, hreadout n]
  exact htarget n g U

/-- Package a bounded-continuous physical observable directly into the existing
gauge-invariant observable algebra once its finite same-root readouts are known
on a dense union of Wilson interpolation images. -/
noncomputable def gaugeInvariantObservableOfDenseInterpolationReadout
    (G : E.PhysicalGaugeAction)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (hDense : Dense G.interpolationImageUnion)
    (O : BoundedContinuousFunction E.PhysicalConfiguration ℝ)
    (target : (n : ℕ) → (E.system n).base.Configuration → ℝ)
    (hreadout : ∀ (n : ℕ) (U : (E.system n).base.Configuration),
      O (E.interpolate n U) = target n U)
    (htarget : ∀ (n : ℕ) (g : G.Symmetry)
      (U : (E.system n).base.Configuration),
      target n
          ((E.system n).base.gaugeTransform (G.latticeGauge n g) U) =
        target n U) :
    physicalYangMillsGaugeInvariantObservableSubalgebra (G.toSymmetryLimit L) :=
  ⟨O,
    G.boundedContinuous_gaugeInvariant_of_dense_interpolation_readout
      hDense O target hreadout htarget⟩

@[simp] theorem gaugeInvariantObservableOfDenseInterpolationReadout_apply
    (G : E.PhysicalGaugeAction)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (hDense : Dense G.interpolationImageUnion)
    (O : BoundedContinuousFunction E.PhysicalConfiguration ℝ)
    (target : (n : ℕ) → (E.system n).base.Configuration → ℝ)
    (hreadout : ∀ (n : ℕ) (U : (E.system n).base.Configuration),
      O (E.interpolate n U) = target n U)
    (htarget : ∀ (n : ℕ) (g : G.Symmetry)
      (U : (E.system n).base.Configuration),
      target n
          ((E.system n).base.gaugeTransform (G.latticeGauge n g) U) =
        target n U)
    (X : E.PhysicalConfiguration) :
    ((G.gaugeInvariantObservableOfDenseInterpolationReadout
        L hDense O target hreadout htarget :
      physicalYangMillsGaugeInvariantObservableSubalgebra
        (G.toSymmetryLimit L)) :
      BoundedContinuousFunction (G.toSymmetryLimit L).Configuration ℝ) X = O X :=
  rfl

end ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.PhysicalGaugeAction

end

end MathlibAnalytic
end MGAP4D
