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

/-- A full binary link field on the integer four-dimensional lattice, stored in
its canonical countable coordinate representation.

The coordinate `Encodable.encode e` stores the value at the integer link `e`.
The carrier `ℕ → Bool` is the standard compact Polish binary sequence space. -/
abbrev Z2InfiniteHypercubicBinaryConfiguration : Type :=
  ℕ → Bool

local instance z2InfiniteHypercubicBinaryConfigurationCompleteSpace :
    CompleteSpace Z2InfiniteHypercubicBinaryConfiguration :=
  Pi.complete

local instance z2InfiniteHypercubicBinaryConfigurationPolishSpace :
    PolishSpace Z2InfiniteHypercubicBinaryConfiguration := by
  infer_instance

/-- Read one integer-lattice link from the canonical binary sequence carrier. -/
def z2InfiniteHypercubicBinaryConfigurationRead
    (B : Z2InfiniteHypercubicBinaryConfiguration)
    (e : IntegerHypercubicEdge) : Bool :=
  B (Encodable.encode e)

/-- Decode one sequence coordinate as an integer-lattice positive link when the
coordinate belongs to the canonical encoding range. -/
def integerHypercubicEdgeOfCode
    (m : ℕ) : Option IntegerHypercubicEdge :=
  Encodable.decode m

@[simp]
theorem integerHypercubicEdgeOfCode_encode
    (e : IntegerHypercubicEdge) :
    integerHypercubicEdgeOfCode (Encodable.encode e) = some e := by
  simp [integerHypercubicEdgeOfCode]

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
lattice and store it in the canonical binary sequence carrier. -/
def z2PeriodicHypercubicConfigurationExtend
    (n : ℕ)
    (A : PeriodicHypercubicEdge n → Z2Gauge) :
    Z2InfiniteHypercubicBinaryConfiguration :=
  fun m =>
    match integerHypercubicEdgeOfCode m with
    | some e => boolEquivZ2Gauge.symm (A (integerHypercubicEdgeToPeriodic n e))
    | none => false

/-- Reading a periodically extended field at an encoded integer link recovers
exactly the corresponding finite periodic link value. -/
@[simp]
theorem z2InfiniteHypercubicBinaryConfigurationRead_extend
    (n : ℕ)
    (A : PeriodicHypercubicEdge n → Z2Gauge)
    (e : IntegerHypercubicEdge) :
    z2InfiniteHypercubicBinaryConfigurationRead
        (z2PeriodicHypercubicConfigurationExtend n A) e =
      boolEquivZ2Gauge.symm (A (integerHypercubicEdgeToPeriodic n e)) := by
  simp [z2InfiniteHypercubicBinaryConfigurationRead,
    z2PeriodicHypercubicConfigurationExtend,
    integerHypercubicEdgeOfCode]

/-- Periodic extension is measurable for the product measurable structures. -/
theorem z2PeriodicHypercubicConfigurationExtend_measurable
    (n : ℕ) :
    Measurable (z2PeriodicHypercubicConfigurationExtend n) := by
  apply measurable_pi_lambda
  intro m
  rcases hCode : integerHypercubicEdgeOfCode m with _ | e
  · simpa [z2PeriodicHypercubicConfigurationExtend, hCode] using
      (measurable_const :
        Measurable
          (fun _ : PeriodicHypercubicEdge n → Z2Gauge => false))
  · simpa [z2PeriodicHypercubicConfigurationExtend, hCode] using
      (measurable_of_finite boolEquivZ2Gauge.symm).comp
        (measurable_pi_apply (integerHypercubicEdgeToPeriodic n e))

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
binary sequence carrier is compact. -/
theorem z2PeriodicHypercubicInfiniteLatticeEmbedding_isTight
    (beta : ℝ)
    (hBeta : 0 < beta) :
    (z2PeriodicHypercubicInfiniteLatticeEmbedding beta hBeta).toLatticeEmbedding.IsTight := by
  letI : CompactSpace
      ((z2PeriodicHypercubicInfiniteLatticeEmbedding beta hBeta)
        .toLatticeEmbedding.PhysicalConfiguration) := by
    change CompactSpace Z2InfiniteHypercubicBinaryConfiguration
    infer_instance
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
