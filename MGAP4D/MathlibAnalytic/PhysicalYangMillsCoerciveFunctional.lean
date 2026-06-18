import MGAP4D.MathlibAnalytic.PhysicalYangMillsAutomaticMarkovTail

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Set

noncomputable section

/-- A measurable coercive functional whose canonical natural-radius sublevels
are compact. This is the purely topological/regularity input for tightness. -/
structure NaturalRadiusCoerciveFunctional
    (X : Type*) [MeasurableSpace X] [TopologicalSpace X] where
  toFun : X → ENNReal
  measurable_toFun : Measurable toFun
  compact_sublevel :
    ∀ n, IsCompact {x | toFun x ≤ ((n + 1 : ℕ) : ENNReal)}

/-- A finite uniform first-moment bound for one fixed coercive functional over a
family of measures. This is the purely probabilistic input for tightness. -/
structure UniformCoerciveFunctionalMomentBound
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    (Phi : NaturalRadiusCoerciveFunctional X)
    (S : Set (Measure X)) where
  momentBound : ENNReal
  momentBound_ne_top : momentBound ≠ ⊤
  uniform_lintegral_le :
    ∀ μ ∈ S, ∫⁻ x, Phi.toFun x ∂μ ≤ momentBound

namespace UniformCoerciveFunctionalMomentBound

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
variable {S : Set (Measure X)}
variable {Phi : NaturalRadiusCoerciveFunctional X}

/-- Combine the topological coercive-functional receipt and probabilistic
moment-bound receipt into the automatic-radius tightness certificate. -/
def toNaturalRadiusCertificate
    (M : UniformCoerciveFunctionalMomentBound Phi S) :
    UniformNaturalRadiusCoerciveMomentCertificate X S :=
  { functional := Phi.toFun
    functional_measurable := Phi.measurable_toFun
    compact_sublevel := Phi.compact_sublevel
    momentBound := M.momentBound
    momentBound_ne_top := M.momentBound_ne_top
    uniform_lintegral_le := M.uniform_lintegral_le }

/-- A finite uniform moment of a coercive functional implies tightness. -/
theorem isTight
    (M : UniformCoerciveFunctionalMomentBound Phi S) :
    IsTightMeasureSet S :=
  M.toNaturalRadiusCertificate.isTight

end UniformCoerciveFunctionalMomentBound

/-- Coercive functional specialized to a fixed physical Yang--Mills carrier. -/
abbrev PhysicalFourDimensionalYangMillsLatticeEmbedding.PhysicalCoerciveFunctional
    (E : PhysicalFourDimensionalYangMillsLatticeEmbedding) :=
  NaturalRadiusCoerciveFunctional E.PhysicalConfiguration

/-- The finite uniform moment receipt stated directly on the original varying
lattice probability spaces for one physical coercive functional. -/
structure PhysicalFourDimensionalYangMillsLatticeEmbedding.LatticeCoerciveFunctionalMomentBound
    (E : PhysicalFourDimensionalYangMillsLatticeEmbedding)
    (Phi : E.PhysicalCoerciveFunctional) where
  momentBound : ENNReal
  momentBound_ne_top : momentBound ≠ ⊤
  uniform_lattice_lintegral_le :
    ∀ n,
      ∫⁻ u, Phi.toFun (E.interpolate n u)
        ∂(E.latticeMeasure n : Measure (E.LatticeConfiguration n)) ≤ momentBound

namespace PhysicalFourDimensionalYangMillsLatticeEmbedding.LatticeCoerciveFunctionalMomentBound

/-- Combine a physical coercive functional with its finite-lattice moment
receipt to obtain the canonical lattice coercive-moment certificate. -/
def toLatticeNaturalRadiusCertificate
    {E : PhysicalFourDimensionalYangMillsLatticeEmbedding}
    {Phi : E.PhysicalCoerciveFunctional}
    (M : E.LatticeCoerciveFunctionalMomentBound Phi) :
    E.LatticeNaturalRadiusCoerciveMomentCertificate :=
  { functional := Phi.toFun
    functional_measurable := Phi.measurable_toFun
    compact_sublevel := Phi.compact_sublevel
    momentBound := M.momentBound
    momentBound_ne_top := M.momentBound_ne_top
    uniform_lattice_lintegral_le := M.uniform_lattice_lintegral_le }

/-- The separated topological and lattice-probabilistic receipts imply
tightness of the embedded laws. -/
theorem isTight
    {E : PhysicalFourDimensionalYangMillsLatticeEmbedding}
    {Phi : E.PhysicalCoerciveFunctional}
    (M : E.LatticeCoerciveFunctionalMomentBound Phi) :
    IsTightMeasureSet E.embeddedMeasureSet :=
  M.toLatticeNaturalRadiusCertificate.isTight

end PhysicalFourDimensionalYangMillsLatticeEmbedding.LatticeCoerciveFunctionalMomentBound

end

end MathlibAnalytic
end MGAP4D
