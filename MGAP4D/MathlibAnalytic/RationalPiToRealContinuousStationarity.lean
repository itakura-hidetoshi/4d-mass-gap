import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.NhdsWithin

/-!
# Rational tuples and real continuous stationarity

This file isolates the generic topology needed to extend common-translation identities
from rational finite tuples to real finite tuples.
-/

namespace MGAP4D

/-- Coordinatewise cast of a rational tuple into a real tuple. -/
def ratPiCast {ι : Type*} (q : ι → ℚ) : ι → ℝ :=
  fun i => (q i : ℝ)

/-- Rational tuples are dense in real tuples for the product topology. -/
theorem ratPiCast_denseRange {ι : Type*} :
    DenseRange (@ratPiCast ι) := by
  simpa only [ratPiCast, Pi.map_apply] using
    (DenseRange.piMap (fun _ : ι => Rat.denseRange_cast))

/-- Two continuous functions on a real product agree everywhere if they agree on every
coordinatewise rational tuple. -/
theorem continuous_eq_of_eq_on_rat_pi
    {ι X : Type*} [TopologicalSpace X] [T2Space X]
    {f g : (ι → ℝ) → X}
    (hf : Continuous f) (hg : Continuous g)
    (hRat : ∀ q : ι → ℚ, f (ratPiCast q) = g (ratPiCast q)) :
    f = g := by
  exact ratPiCast_denseRange.equalizer hf hg (by
    funext q
    exact hRat q)

/-- Add one common real shift to every coordinate of a real tuple. -/
def realCommonShift {ι : Type*} (time : ι → ℝ) (r : ℝ) : ι → ℝ :=
  fun i => time i + r

/-- For fixed shift, common translation is continuous in the tuple. -/
theorem realCommonShift_continuous_time {ι : Type*} (r : ℝ) :
    Continuous (fun time : ι → ℝ => realCommonShift time r) := by
  exact continuous_pi (fun i => (continuous_apply i).add continuous_const)

/-- For fixed tuple, common translation is continuous in the real shift. -/
theorem realCommonShift_continuous_shift {ι : Type*} (time : ι → ℝ) :
    Continuous (fun r : ℝ => realCommonShift time r) := by
  exact continuous_pi (fun _ => continuous_const.add continuous_id)

end MGAP4D
