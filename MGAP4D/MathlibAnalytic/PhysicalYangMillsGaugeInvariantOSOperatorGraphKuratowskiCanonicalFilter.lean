import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSOperatorGraphKuratowskiZeroShift
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace LinearPMap

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- The admissible rescaled-defect time filter is nontrivial.  The admissible
predicate holds eventually in the positive small-time filter, so every
small-time filter set contains an admissible time. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectTimeFilter_neBot_of_eventuallyLinearBound
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope) :
    NeBot G.admissibleRescaledDefectTimeFilter := by
  unfold VacuumSemigroupGapSlope.admissibleRescaledDefectTimeFilter
  letI : NeBot (nhdsWithin (0 : NNReal) (Ioi 0)) :=
    nhdsWithin_Ioi_neBot le_rfl
  apply Filter.comap_neBot
  intro s hs
  have hAdmissible :
      ∀ᶠ t : NNReal in nhdsWithin 0 (Ioi 0),
        0 < t ∧ (G.mass / 2) * (t : ℝ) ≤ 1 - G.decayFactor t := by
    filter_upwards
      [self_mem_nhdsWithin, G.eventually_linear_defect_lower_bound T]
        with t ht hLinear
    exact ⟨ht, hLinear⟩
  have hIntersection :
      s ∩ {t : NNReal |
        0 < t ∧ (G.mass / 2) * (t : ℝ) ≤ 1 - G.decayFactor t} ∈
        nhdsWithin 0 (Ioi 0) :=
    inter_mem hs hAdmissible
  rcases Filter.nonempty_of_mem hIntersection with ⟨t, htS, htAdmissible⟩
  exact ⟨⟨t, htAdmissible⟩, htS⟩

/-- Canonical typeclass instance for the admissible positive small-time
filter. -/
instance VacuumSemigroupGapSlope.instNeBotAdmissibleRescaledDefectTimeFilterFromGapSlope
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope) :
    NeBot G.admissibleRescaledDefectTimeFilter :=
  G.admissibleRescaledDefectTimeFilter_neBot_of_eventuallyLinearBound T

/-- Final canonical formulation: the ordinary rescaled-defect graphs converge
in both Painlevé–Kuratowski senses to the graph of the closed continuum
Hamiltonian, with no shift, source, time-net, or filter-nontriviality argument
exposed to the theorem user. -/
theorem VacuumSemigroupGapSlope.canonicalFilter_rescaledDefectGraph_kuratowskiLimits_eq_continuumHamiltonianGraph
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) :
    FilterSet.kuratowskiInnerLimit G.admissibleRescaledDefectTimeFilter
        (G.rescaledDefectGraphFamily T hInnerSymmetric
          (fun tau : G.AdmissibleRescaledDefectTime => tau)) =
      G.continuumHamiltonianGraph T hSelf ∧
    FilterSet.kuratowskiOuterLimit G.admissibleRescaledDefectTimeFilter
        (G.rescaledDefectGraphFamily T hInnerSymmetric
          (fun tau : G.AdmissibleRescaledDefectTime => tau)) =
      G.continuumHamiltonianGraph T hSelf := by
  exact
    G.rescaledDefectGraph_kuratowskiLimits_eq_continuumHamiltonianGraph
      T hP hInnerSymmetric hSelf

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
