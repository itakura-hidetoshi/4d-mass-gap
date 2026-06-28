import MGAP4D.MathlibAnalytic.PhysicalYangMillsCoerciveFunctional
import MGAP4D.MathlibAnalytic.PhysicalYangMillsProkhorovLimit

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A physical coercive functional and a finite uniform moment bound for the
embedded laws supply the tightness input for Prokhorov. -/
theorem PhysicalFourDimensionalYangMillsLatticeEmbedding.isTight_of_coerciveFunctionalMomentBound
    (E : PhysicalFourDimensionalYangMillsLatticeEmbedding)
    (Phi : E.PhysicalCoerciveFunctional)
    (M : UniformCoerciveFunctionalMomentBound Phi E.embeddedMeasureSet) :
    E.IsTight :=
  M.isTight

/-- A physical coercive functional and a finite uniform moment bound stated on
the original lattice laws supply the tightness input after interpolation. -/
theorem PhysicalFourDimensionalYangMillsLatticeEmbedding.isTight_of_latticeCoerciveFunctionalMomentBound
    (E : PhysicalFourDimensionalYangMillsLatticeEmbedding)
    (Phi : E.PhysicalCoerciveFunctional)
    (M : E.LatticeCoerciveFunctionalMomentBound Phi) :
    E.IsTight :=
  M.isTight

/-- Separated topological and common-carrier moment receipts produce a physical
continuum weak limit. -/
noncomputable def physical_yang_mills_weak_limit_of_coerciveFunctionalMomentBound
    (E : PhysicalFourDimensionalYangMillsLatticeEmbedding)
    (Phi : E.PhysicalCoerciveFunctional)
    (M : UniformCoerciveFunctionalMomentBound Phi E.embeddedMeasureSet) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  physical_yang_mills_weak_limit_of_tight E
    (E.isTight_of_coerciveFunctionalMomentBound Phi M)

/-- Separated physical compactness and finite-lattice moment receipts produce a
physical continuum weak limit directly. -/
noncomputable def
    physical_yang_mills_weak_limit_of_latticeCoerciveFunctionalMomentBound
    (E : PhysicalFourDimensionalYangMillsLatticeEmbedding)
    (Phi : E.PhysicalCoerciveFunctional)
    (M : E.LatticeCoerciveFunctionalMomentBound Phi) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  physical_yang_mills_weak_limit_of_tight E
    (E.isTight_of_latticeCoerciveFunctionalMomentBound Phi M)

/-- Compact-gauge Wilson specialization of the separated common-carrier
coercive-functional route. -/
noncomputable def
    continuous_compact_gauge_wilson_weak_limit_of_coerciveFunctionalMomentBound
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional)
    (M : UniformCoerciveFunctionalMomentBound
      Phi E.toLatticeEmbedding.embeddedMeasureSet) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  physical_yang_mills_weak_limit_of_coerciveFunctionalMomentBound
    E.toLatticeEmbedding Phi M

/-- Compact-gauge Wilson specialization requiring only a physical coercive
functional and its finite uniform moment estimate on the original Gibbs laws. -/
noncomputable def
    continuous_compact_gauge_wilson_weak_limit_of_latticeCoerciveFunctionalMomentBound
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional)
    (M : E.toLatticeEmbedding.LatticeCoerciveFunctionalMomentBound Phi) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  physical_yang_mills_weak_limit_of_latticeCoerciveFunctionalMomentBound
    E.toLatticeEmbedding Phi M

end

end MathlibAnalytic
end MGAP4D
