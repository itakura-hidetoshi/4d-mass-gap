import MGAP4D.MathlibAnalytic.PhysicalYangMillsLatticeMomentCertificate
import Mathlib.Topology.Instances.ENNReal.Lemmas

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Set

noncomputable section

/-- A finite extended-nonnegative constant divided by the canonical radii
`n + 1` tends to zero. -/
theorem ennreal_tendsto_const_div_natCast_add_one
    (C : ENNReal) (hC : C ≠ ⊤) :
    Tendsto (fun n : ℕ => C / ((n + 1 : ℕ) : ENNReal)) atTop (nhds 0) := by
  have hInv :
      Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ENNReal))⁻¹) atTop (nhds 0) :=
    (tendsto_add_atTop_iff_nat 1).2 ENNReal.tendsto_inv_nat_nhds_zero
  have hMul :
      Tendsto
        (fun n : ℕ => C * (((n + 1 : ℕ) : ENNReal))⁻¹)
        atTop (nhds (C * 0)) :=
    ENNReal.Tendsto.const_mul hInv (Or.inr hC)
  simpa [div_eq_mul_inv] using hMul

/-- Coercive-moment data using the canonical compact sublevels
`functional ≤ n + 1`. Finiteness of the moment bound automatically supplies
the vanishing Markov tail. -/
structure UniformNaturalRadiusCoerciveMomentCertificate
    (X : Type*) [MeasurableSpace X] [TopologicalSpace X]
    (S : Set (Measure X)) where
  functional : X → ENNReal
  functional_measurable : Measurable functional
  compact_sublevel :
    ∀ n, IsCompact {x | functional x ≤ ((n + 1 : ℕ) : ENNReal)}
  momentBound : ENNReal
  momentBound_ne_top : momentBound ≠ ⊤
  uniform_lintegral_le :
    ∀ μ ∈ S, ∫⁻ x, functional x ∂μ ≤ momentBound

namespace UniformNaturalRadiusCoerciveMomentCertificate

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
variable {S : Set (Measure X)}

/-- Convert the canonical-radius data to the general coercive-moment
certificate without requesting a separate tail-limit proof. -/
def toCoerciveMomentCertificate
    (C : UniformNaturalRadiusCoerciveMomentCertificate X S) :
    UniformCoerciveMomentCertificate X S :=
  { functional := C.functional
    functional_measurable := C.functional_measurable
    radius := fun n => ((n + 1 : ℕ) : ENNReal)
    radius_ne_zero := fun n => by simp
    radius_ne_top := fun n => by simp
    compact_sublevel := C.compact_sublevel
    momentBound := C.momentBound
    uniform_lintegral_le := C.uniform_lintegral_le
    markovTail_tendsto_zero :=
      ennreal_tendsto_const_div_natCast_add_one
        C.momentBound C.momentBound_ne_top }

/-- Canonical-radius coercive moments imply tightness. -/
theorem isTight
    (C : UniformNaturalRadiusCoerciveMomentCertificate X S) :
    IsTightMeasureSet S :=
  C.toCoerciveMomentCertificate.isTight

end UniformNaturalRadiusCoerciveMomentCertificate

/-- Canonical-radius coercive moment data specialized to the embedded physical
lattice laws. -/
abbrev PhysicalFourDimensionalYangMillsLatticeEmbedding.NaturalRadiusCoerciveMomentCertificate
    (E : PhysicalFourDimensionalYangMillsLatticeEmbedding) :=
  UniformNaturalRadiusCoerciveMomentCertificate
    E.PhysicalConfiguration E.embeddedMeasureSet

/-- The finite-lattice analytic input with canonical physical sublevels
`functional ≤ n + 1`. Only a finite uniform moment bound is required. -/
structure PhysicalFourDimensionalYangMillsLatticeEmbedding.LatticeNaturalRadiusCoerciveMomentCertificate
    (E : PhysicalFourDimensionalYangMillsLatticeEmbedding) where
  functional : E.PhysicalConfiguration → ENNReal
  functional_measurable : Measurable functional
  compact_sublevel :
    ∀ n, IsCompact {x | functional x ≤ ((n + 1 : ℕ) : ENNReal)}
  momentBound : ENNReal
  momentBound_ne_top : momentBound ≠ ⊤
  uniform_lattice_lintegral_le :
    ∀ n,
      ∫⁻ u, functional (E.interpolate n u)
        ∂(E.latticeMeasure n : Measure (E.LatticeConfiguration n)) ≤ momentBound

namespace PhysicalFourDimensionalYangMillsLatticeEmbedding.LatticeNaturalRadiusCoerciveMomentCertificate

/-- Convert the canonical finite-lattice estimate to the general lattice-side
certificate, deriving the Markov-tail limit automatically. -/
def toLatticeCoerciveMomentCertificate
    {E : PhysicalFourDimensionalYangMillsLatticeEmbedding}
    (C : E.LatticeNaturalRadiusCoerciveMomentCertificate) :
    E.LatticeCoerciveMomentCertificate :=
  { functional := C.functional
    functional_measurable := C.functional_measurable
    radius := fun n => ((n + 1 : ℕ) : ENNReal)
    radius_ne_zero := fun n => by simp
    radius_ne_top := fun n => by simp
    compact_sublevel := C.compact_sublevel
    momentBound := C.momentBound
    uniform_lattice_lintegral_le := C.uniform_lattice_lintegral_le
    markovTail_tendsto_zero :=
      ennreal_tendsto_const_div_natCast_add_one
        C.momentBound C.momentBound_ne_top }

/-- A finite uniform lattice moment bound with canonical compact sublevels
implies tightness of the embedded physical laws. -/
theorem isTight
    {E : PhysicalFourDimensionalYangMillsLatticeEmbedding}
    (C : E.LatticeNaturalRadiusCoerciveMomentCertificate) :
    IsTightMeasureSet E.embeddedMeasureSet :=
  C.toLatticeCoerciveMomentCertificate.isTight

end PhysicalFourDimensionalYangMillsLatticeEmbedding.LatticeNaturalRadiusCoerciveMomentCertificate

end

end MathlibAnalytic
end MGAP4D
