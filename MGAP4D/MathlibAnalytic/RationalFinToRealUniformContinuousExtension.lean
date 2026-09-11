import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.UniformSpace.UniformEmbedding
import MGAP4D.MathlibAnalytic.RationalPiToRealContinuousStationarity

/-!
# Uniformly continuous extension from rational finite tuples to real finite tuples

For a finite labelled tuple, coordinatewise coercion from `ℚ` to `ℝ` is an
isometry with dense range.  Hence every uniformly continuous scalar function on
rational tuples has a canonical uniformly continuous extension to real tuples.

This isolates the precise analytic input needed to construct real insertion-time
Schwinger functions from rational insertion-time data.
-/

namespace MGAP4D

noncomputable section

/-- Coordinatewise coercion `(Fin n → ℚ) → (Fin n → ℝ)` is an isometry. -/
theorem ratFinCast_isometry (n : ℕ) :
    Isometry (@ratPiCast (Fin n)) := by
  have hcoord : ∀ _ : Fin n, Isometry (fun q : ℚ => (q : ℝ)) := by
    intro i
    exact Isometry.of_dist_eq Rat.dist_cast
  simpa [ratPiCast] using
    (Isometry.piMap (fun _ : Fin n => fun q : ℚ => (q : ℝ)) hcoord)

/-- Coordinatewise coercion on a finite rational tuple is uniform inducing. -/
theorem ratFinCast_isUniformInducing (n : ℕ) :
    IsUniformInducing (@ratPiCast (Fin n)) :=
  (ratFinCast_isometry n).isUniformInducing

/-- Canonical extension of a scalar function from rational finite tuples to real
finite tuples.  Continuity properties are supplied by the following theorems. -/
def ratFinUniformlyExtend (n : ℕ) (f : (Fin n → ℚ) → ℝ) :
    (Fin n → ℝ) → ℝ :=
  ((ratFinCast_isUniformInducing n).isDenseInducing
    (ratPiCast_denseRange (ι := Fin n))).extend f

/-- A uniformly continuous rational-tuple function has a uniformly continuous
canonical real-tuple extension. -/
theorem ratFinUniformlyExtend_uniformContinuous
    (n : ℕ) (f : (Fin n → ℚ) → ℝ)
    (hf : UniformContinuous f) :
    UniformContinuous (ratFinUniformlyExtend n f) := by
  simpa [ratFinUniformlyExtend] using
    (uniformContinuous_uniformly_extend
      (ratFinCast_isUniformInducing n)
      (ratPiCast_denseRange (ι := Fin n)) hf)

/-- In particular, the canonical extension is continuous. -/
theorem ratFinUniformlyExtend_continuous
    (n : ℕ) (f : (Fin n → ℚ) → ℝ)
    (hf : UniformContinuous f) :
    Continuous (ratFinUniformlyExtend n f) :=
  (ratFinUniformlyExtend_uniformContinuous n f hf).continuous

/-- The canonical extension agrees exactly with the original function on every
rational tuple. -/
theorem ratFinUniformlyExtend_ratPiCast
    (n : ℕ) (f : (Fin n → ℚ) → ℝ)
    (hf : UniformContinuous f) (time : Fin n → ℚ) :
    ratFinUniformlyExtend n f (ratPiCast time) = f time := by
  simpa [ratFinUniformlyExtend] using
    (uniformly_extend_of_ind
      (ratFinCast_isUniformInducing n)
      (ratPiCast_denseRange (ι := Fin n)) hf time)

/-- The canonical extension is the unique continuous real-tuple function with
the prescribed rational restriction. -/
theorem ratFinUniformlyExtend_unique
    (n : ℕ) (f : (Fin n → ℚ) → ℝ)
    (g : (Fin n → ℝ) → ℝ)
    (hg : ∀ time : Fin n → ℚ, g (ratPiCast time) = f time)
    (hcontinuous : Continuous g) :
    ratFinUniformlyExtend n f = g := by
  simpa [ratFinUniformlyExtend] using
    (uniformly_extend_unique
      (ratFinCast_isUniformInducing n)
      (ratPiCast_denseRange (ι := Fin n)) hg hcontinuous)

end

end MGAP4D
