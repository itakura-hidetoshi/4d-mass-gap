import MGAP4D.MathlibAnalytic.PhysicalYangMillsZ2PeriodicCanonicalCoerciveMomentClustering
import Mathlib.Data.Countable.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

/-- Vertices of the integer four-dimensional hypercubic lattice. -/
abbrev IntegerHypercubicVertex : Type :=
  Fin 4 → ℤ

/-- Positively oriented links of the integer four-dimensional hypercubic
lattice. -/
abbrev IntegerHypercubicEdge : Type :=
  IntegerHypercubicVertex × Fin 4

local instance : Countable IntegerHypercubicVertex := inferInstance
local instance : Countable IntegerHypercubicEdge := inferInstance

/-- A full binary link field on the integer four-dimensional lattice.

The carrier is a countable product of two-point discrete spaces, hence is a
compact Polish space. -/
abbrev Z2InfiniteHypercubicBinaryConfiguration : Type :=
  IntegerHypercubicEdge → Bool

/-- Reduce an integer-lattice vertex modulo the periodic side length. -/
def integerHypercubicVertexToPeriodic
    (n : ℕ)
    (x : IntegerHypercubicVertex) :
    PeriodicHypercubicVertex n :=
  fun mu => (x mu : ZMod n)

/-- Reduce an integer-lattice positive link modulo the periodic side length. -/
def integerHypercubicEdgeToPeriodic
    (n : ℕ)
    (e : IntegerHypercubicEdge) :
    PeriodicHypercubicEdge n :=
  (integerHypercubicVertexToPeriodic n e.1, e.2)

/-- Periodically extend a finite `Z₂` link configuration to the full integer
lattice and encode each group value by its canonical Boolean representative. -/
def z2PeriodicHypercubicConfigurationExtend
    (n : ℕ)
    (A : PeriodicHypercubicEdge n → Z2Gauge) :
    Z2InfiniteHypercubicBinaryConfiguration :=
  fun e => boolEquivZ2Gauge.symm (A (integerHypercubicEdgeToPeriodic n e))

@[simp]
theorem z2PeriodicHypercubicConfigurationExtend_apply
    (n : ℕ)
    (A : PeriodicHypercubicEdge n → Z2Gauge)
    (e : IntegerHypercubicEdge) :
    z2PeriodicHypercubicConfigurationExtend n A e =
      boolEquivZ2Gauge.symm (A (integerHypercubicEdgeToPeriodic n e)) :=
  rfl

/-- Periodic extension is measurable for the product measurable structures. -/
theorem z2PeriodicHypercubicConfigurationExtend_measurable
    (n : ℕ) :
    Measurable (z2PeriodicHypercubicConfigurationExtend n) := by
  exact measurable_pi_lambda _ (fun e =>
    (measurable_of_finite boolEquivZ2Gauge.symm).comp
      (measurable_pi_apply (integerHypercubicEdgeToPeriodic n e)))

/-- Concrete common-carrier interpolation of every canonical finite periodic
`Z₂` Gibbs system into the compact binary link-field carrier.

This is an infinite-lattice periodic extension. It is not, by itself, a
continuum gauge-field interpolation. -/
noncomputable def z2PeriodicHypercubicInfiniteLatticeInterpolation
    (beta : ℝ)
    (hBeta : 0 < beta) :
    PhysicalYangMillsZ2PeriodicCanonicalInterpolation beta hBeta :=
  { PhysicalConfiguration := Z2InfiniteHypercubicBinaryConfiguration
    interpolate := fun k =>
      z2PeriodicHypercubicConfigurationExtend
        (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
    interpolate_measurable := fun k =>
      z2PeriodicHypercubicConfigurationExtend_measurable
        (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k) }

/-- The canonical finite periodic laws, explicit scaling schedule, and concrete
periodic extension assembled into one lattice embedding. -/
noncomputable def z2PeriodicHypercubicInfiniteLatticeEmbedding
    (beta : ℝ)
    (hBeta : 0 < beta) :
    PhysicalYangMillsZ2PeriodicCanonicalLatticeEmbedding beta hBeta :=
  (z2PeriodicHypercubicInfiniteLatticeInterpolation beta hBeta).toCanonicalLatticeEmbedding

/-- The embedded periodic `Z₂` laws are automatically tight because the common
binary link-field carrier is compact. -/
theorem z2PeriodicHypercubicInfiniteLatticeEmbedding_isTight
    (beta : ℝ)
    (hBeta : 0 < beta) :
    (z2PeriodicHypercubicInfiniteLatticeEmbedding beta hBeta).toLatticeEmbedding.IsTight := by
  exact MeasureTheory.IsTightMeasureSet.of_compactSpace

/-- Prokhorov compactness extracts a weakly convergent subsequence of the actual
periodic Gibbs laws on the common infinite-lattice binary carrier. -/
theorem z2PeriodicHypercubicInfiniteLatticeProkhorov_exists
    (beta : ℝ)
    (hBeta : 0 < beta) :
    Nonempty
      (PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
        (z2PeriodicHypercubicInfiniteLatticeEmbedding beta hBeta).toLatticeEmbedding) :=
  physical_yang_mills_prokhorov_subsequence_exists
    (z2PeriodicHypercubicInfiniteLatticeEmbedding beta hBeta).toLatticeEmbedding
    (z2PeriodicHypercubicInfiniteLatticeEmbedding_isTight beta hBeta)

/-- A canonical noncomputable choice of one subsequential infinite-lattice weak
limit. -/
noncomputable def z2PeriodicHypercubicInfiniteLatticeProkhorovLimit
    (beta : ℝ)
    (hBeta : 0 < beta) :
    PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      (z2PeriodicHypercubicInfiniteLatticeEmbedding beta hBeta).toLatticeEmbedding :=
  (z2PeriodicHypercubicInfiniteLatticeProkhorov_exists beta hBeta).some

/-- The selected Prokhorov subsequence as a physical weak-limit record with the
canonical scaling metadata. -/
noncomputable def z2PeriodicHypercubicInfiniteLatticeWeakLimit
    (beta : ℝ)
    (hBeta : 0 < beta) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  (z2PeriodicHypercubicInfiniteLatticeProkhorovLimit beta hBeta).toWeakLimit

end

end MathlibAnalytic
end MGAP4D
