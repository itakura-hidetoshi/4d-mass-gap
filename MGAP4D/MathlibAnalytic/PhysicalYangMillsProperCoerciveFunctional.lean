import MGAP4D.MathlibAnalytic.PhysicalYangMillsCoerciveFunctional
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

namespace MGAP4D
namespace MathlibAnalytic

open Set

noncomputable section

namespace NaturalRadiusCoerciveFunctional

/-- A proper extended-nonnegative functional on a Borel space automatically has
compact natural-radius sublevels. Since `ENNReal` is compact, this route is most
useful when the physical carrier itself is compact. -/
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
          IsCompact
            (functional ⁻¹'
              Set.Icc 0 (((n + 1 : ℕ) : ENNReal))) :=
        functional_proper.isCompact_preimage isCompact_Icc
      have hSet :
          {x | functional x ≤ ((n + 1 : ℕ) : ENNReal)} =
            functional ⁻¹' Set.Icc 0 (((n + 1 : ℕ) : ENNReal)) := by
        ext x
        simp
      rw [hSet]
      exact hCompact }

/-- A proper nonnegative-real functional yields the practically useful coercive
receipt on a possibly noncompact physical carrier. Its finite `NNReal`
sublevels are compact, and coercion supplies the required `ENNReal` observable. -/
def ofProperNNReal
    {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (functional : X → NNReal)
    (functional_proper : IsProperMap functional) :
    NaturalRadiusCoerciveFunctional X :=
  { toFun := fun x => (functional x : ENNReal)
    measurable_toFun :=
      (ENNReal.continuous_coe.comp functional_proper.continuous).measurable
    compact_sublevel := by
      intro n
      have hCompact :
          IsCompact
            (functional ⁻¹'
              Set.Icc 0 (((n + 1 : ℕ) : NNReal))) :=
        functional_proper.isCompact_preimage isCompact_Icc
      have hSet :
          {x | (functional x : ENNReal) ≤ ((n + 1 : ℕ) : ENNReal)} =
            functional ⁻¹' Set.Icc 0 (((n + 1 : ℕ) : NNReal)) := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Icc,
          zero_le, true_and]
        constructor <;> intro h <;> exact_mod_cast h
      rw [hSet]
      exact hCompact }

end NaturalRadiusCoerciveFunctional

/-- A proper `ENNReal`-valued physical functional gives the canonical receipt
for a fixed lattice embedding. -/
def PhysicalFourDimensionalYangMillsLatticeEmbedding.physicalCoerciveFunctional_ofProper
    (E : PhysicalFourDimensionalYangMillsLatticeEmbedding)
    (functional : E.PhysicalConfiguration → ENNReal)
    (functional_proper : IsProperMap functional) :
    E.PhysicalCoerciveFunctional :=
  NaturalRadiusCoerciveFunctional.ofProper functional functional_proper

/-- A proper `NNReal`-valued physical functional gives a coercive receipt on a
possibly noncompact physical carrier. -/
def PhysicalFourDimensionalYangMillsLatticeEmbedding.physicalCoerciveFunctional_ofProperNNReal
    (E : PhysicalFourDimensionalYangMillsLatticeEmbedding)
    (functional : E.PhysicalConfiguration → NNReal)
    (functional_proper : IsProperMap functional) :
    E.PhysicalCoerciveFunctional :=
  NaturalRadiusCoerciveFunctional.ofProperNNReal functional functional_proper

/-- Compact-gauge Wilson specialization of the proper `ENNReal` constructor. -/
def ContinuousCompactGaugeWilsonPhysicalEmbedding.physicalCoerciveFunctional_ofProper
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (functional : E.PhysicalConfiguration → ENNReal)
    (functional_proper : IsProperMap functional) :
    E.toLatticeEmbedding.PhysicalCoerciveFunctional :=
  NaturalRadiusCoerciveFunctional.ofProper functional functional_proper

/-- Compact-gauge Wilson specialization of the proper `NNReal` constructor. -/
def ContinuousCompactGaugeWilsonPhysicalEmbedding.physicalCoerciveFunctional_ofProperNNReal
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (functional : E.PhysicalConfiguration → NNReal)
    (functional_proper : IsProperMap functional) :
    E.toLatticeEmbedding.PhysicalCoerciveFunctional :=
  NaturalRadiusCoerciveFunctional.ofProperNNReal functional functional_proper

end

end MathlibAnalytic
end MGAP4D
