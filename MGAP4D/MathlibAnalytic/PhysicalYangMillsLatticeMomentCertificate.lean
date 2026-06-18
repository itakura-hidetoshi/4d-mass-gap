import MGAP4D.MathlibAnalytic.PhysicalYangMillsLatticeMomentTransfer

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Set

noncomputable section

structure PhysicalFourDimensionalYangMillsLatticeEmbedding.LatticeCoerciveMomentCertificate
    (E : PhysicalFourDimensionalYangMillsLatticeEmbedding) where
  functional : E.PhysicalConfiguration → ENNReal
  functional_measurable : Measurable functional
  radius : ℕ → ENNReal
  radius_ne_zero : ∀ n, radius n ≠ 0
  radius_ne_top : ∀ n, radius n ≠ ⊤
  compact_sublevel : ∀ n, IsCompact {x | functional x ≤ radius n}
  momentBound : ENNReal
  uniform_lattice_lintegral_le :
    ∀ n,
      ∫⁻ u, functional (E.interpolate n u)
        ∂(E.latticeMeasure n : Measure (E.LatticeConfiguration n)) ≤ momentBound
  markovTail_tendsto_zero :
    Tendsto (fun n => momentBound / radius n) atTop (nhds 0)

namespace PhysicalFourDimensionalYangMillsLatticeEmbedding.LatticeCoerciveMomentCertificate

/-- Convert a lattice-side estimate to the common-carrier certificate. -/
def toCoerciveMomentCertificate
    {E : PhysicalFourDimensionalYangMillsLatticeEmbedding}
    (C : E.LatticeCoerciveMomentCertificate) :
    E.CoerciveMomentCertificate :=
  { functional := C.functional
    functional_measurable := C.functional_measurable
    radius := C.radius
    radius_ne_zero := C.radius_ne_zero
    radius_ne_top := C.radius_ne_top
    compact_sublevel := C.compact_sublevel
    momentBound := C.momentBound
    uniform_lintegral_le := by
      intro μ hμ
      rcases hμ with ⟨ν, ⟨n, rfl⟩, rfl⟩
      rw [E.lintegral_embeddedMeasure C.functional C.functional_measurable n]
      exact C.uniform_lattice_lintegral_le n
    markovTail_tendsto_zero := C.markovTail_tendsto_zero }

/-- The lattice-side certificate implies tightness after interpolation. -/
theorem isTight
    {E : PhysicalFourDimensionalYangMillsLatticeEmbedding}
    (C : E.LatticeCoerciveMomentCertificate) :
    IsTightMeasureSet E.embeddedMeasureSet :=
  C.toCoerciveMomentCertificate.isTight

end PhysicalFourDimensionalYangMillsLatticeEmbedding.LatticeCoerciveMomentCertificate

end

end MathlibAnalytic
end MGAP4D
