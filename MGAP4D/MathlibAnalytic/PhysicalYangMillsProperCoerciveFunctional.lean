import MGAP4D.MathlibAnalytic.PhysicalYangMillsCoerciveFunctional
import Mathlib.Topology.Maps.Proper.Basic

namespace MGAP4D
namespace MathlibAnalytic

open Set

noncomputable section

namespace NaturalRadiusCoerciveFunctional

/-- A proper extended-nonnegative functional on a Borel space automatically has
compact natural-radius sublevels and therefore defines a coercive functional. -/
def ofProper
    {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (functional : X → ENNReal)
    (functional_proper : IsProperMap functional) :
    NaturalRadiusCoerciveFunctional X :=
  { toFun := functional
    measurable_toFun := functional_proper.continuous.measurable
    compact_sublevel := by
      intro n
      have hCompact :
          IsCompact (functional ⁻¹' Set.Iic (((n + 1 : ℕ) : ENNReal))) :=
        functional_proper.isCompact_preimage isCompact_Iic
      simpa only [Set.preimage_setOf_eq, Set.mem_Iic] using hCompact }

end NaturalRadiusCoerciveFunctional

/-- A proper physical functional gives the canonical coercive-functional receipt
for a fixed lattice embedding. -/
def PhysicalFourDimensionalYangMillsLatticeEmbedding.physicalCoerciveFunctional_ofProper
    (E : PhysicalFourDimensionalYangMillsLatticeEmbedding)
    (functional : E.PhysicalConfiguration → ENNReal)
    (functional_proper : IsProperMap functional) :
    E.PhysicalCoerciveFunctional :=
  NaturalRadiusCoerciveFunctional.ofProper functional functional_proper

/-- Compact-gauge Wilson specialization of the proper-functional constructor. -/
def ContinuousCompactGaugeWilsonPhysicalEmbedding.physicalCoerciveFunctional_ofProper
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (functional : E.PhysicalConfiguration → ENNReal)
    (functional_proper : IsProperMap functional) :
    E.toLatticeEmbedding.PhysicalCoerciveFunctional :=
  NaturalRadiusCoerciveFunctional.ofProper functional functional_proper

end

end MathlibAnalytic
end MGAP4D
