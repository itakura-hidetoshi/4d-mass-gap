import MGAP4D.MathlibAnalytic.FilterKuratowskiLowerLimit
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSKuratowskiDefectGraphOuterLimit
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

/-- A convergent eventually admissible recovery selection places the canonical
continuum resolvent graph point in the filter Painlevé–Kuratowski lower limit. -/
theorem VacuumSemigroupGapSlope.approximateShiftedDefectGraphFamily_canonical_mem_kuratowskiLowerLimit_of_recovery
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) {ι : Type*} (l : Filter ι)
    {lambdaNet : ι → ℝ} {lambda : ℝ} (hlambda : lambda < G.mass / 2)
    {yNet : ι → P.VacuumOrthogonalHilbert} {y : P.VacuumOrthogonalHilbert}
    {tau : ι → G.AdmissibleRescaledDefectTime} {epsilon : ι → ℝ}
    (v : ι → P.VacuumOrthogonalHilbert × P.VacuumOrthogonalHilbert)
    (hv : Tendsto v l
      (nhds (G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf hlambda y,
        T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
          (G.vacuumOrthogonalContinuumRealResolventDomainPoint
            T hP hInnerSymmetric hSelf hlambda y))))
    (hMem : ∀ᶠ i in l,
      v i ∈ G.approximateShiftedDefectGraphFamily
        T hInnerSymmetric tau lambdaNet yNet epsilon i) :
    (G.vacuumOrthogonalContinuumRealResolvent
        T hP hInnerSymmetric hSelf hlambda y,
      T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
        (G.vacuumOrthogonalContinuumRealResolventDomainPoint
          T hP hInnerSymmetric hSelf hlambda y)) ∈
      FilterSet.kuratowskiLowerLimit l
        (G.approximateShiftedDefectGraphFamily
          T hInnerSymmetric tau lambdaNet yNet epsilon) := by
  apply FilterSet.convergentSelectionLowerLimit_subset_kuratowskiLowerLimit
    l (G.approximateShiftedDefectGraphFamily
      T hInnerSymmetric tau lambdaNet yNet epsilon)
  exact ⟨v, hv, hMem⟩

/-- Once a recovery selection exists, the full filter Painlevé–Kuratowski lower
and outer limits both equal the singleton canonical continuum graph point. -/
theorem VacuumSemigroupGapSlope.approximateShiftedDefectGraphFamily_kuratowskiLimits_eq_singleton_of_recovery
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) {ι : Type*} (l : Filter ι)
    [NeBot l]
    {lambdaNet : ι → ℝ} {lambda : ℝ} (hlambda : lambda < G.mass / 2)
    {yNet : ι → P.VacuumOrthogonalHilbert} {y : P.VacuumOrthogonalHilbert}
    {tau : ι → G.AdmissibleRescaledDefectTime} {epsilon : ι → ℝ}
    (hTau : Tendsto tau l G.admissibleRescaledDefectTimeFilter)
    (hLambda : Tendsto lambdaNet l (nhds lambda)) (hy : Tendsto yNet l (nhds y))
    (hEpsilon : Tendsto epsilon l (nhds 0))
    (v : ι → P.VacuumOrthogonalHilbert × P.VacuumOrthogonalHilbert)
    (hv : Tendsto v l
      (nhds (G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf hlambda y,
        T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
          (G.vacuumOrthogonalContinuumRealResolventDomainPoint
            T hP hInnerSymmetric hSelf hlambda y))))
    (hMem : ∀ᶠ i in l,
      v i ∈ G.approximateShiftedDefectGraphFamily
        T hInnerSymmetric tau lambdaNet yNet epsilon i) :
    FilterSet.kuratowskiOuterLimit l
        (G.approximateShiftedDefectGraphFamily
          T hInnerSymmetric tau lambdaNet yNet epsilon) =
      {(G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf hlambda y,
        T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
          (G.vacuumOrthogonalContinuumRealResolventDomainPoint
            T hP hInnerSymmetric hSelf hlambda y))} ∧
    FilterSet.kuratowskiLowerLimit l
        (G.approximateShiftedDefectGraphFamily
          T hInnerSymmetric tau lambdaNet yNet epsilon) =
      {(G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf hlambda y,
        T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
          (G.vacuumOrthogonalContinuumRealResolventDomainPoint
            T hP hInnerSymmetric hSelf hlambda y))} := by
  let canonical : P.VacuumOrthogonalHilbert × P.VacuumOrthogonalHilbert :=
    (G.vacuumOrthogonalContinuumRealResolvent
        T hP hInnerSymmetric hSelf hlambda y,
      T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
        (G.vacuumOrthogonalContinuumRealResolventDomainPoint
          T hP hInnerSymmetric hSelf hlambda y))
  have hOuter :
      FilterSet.kuratowskiOuterLimit l
          (G.approximateShiftedDefectGraphFamily
            T hInnerSymmetric tau lambdaNet yNet epsilon) ⊆ {canonical} := by
    simpa [canonical] using
      G.approximateShiftedDefectGraphFamily_kuratowskiOuterLimit_subset_singleton
        T hP hInnerSymmetric hSelf l hlambda hTau hLambda hy hEpsilon
  have hLower : canonical ∈
      FilterSet.kuratowskiLowerLimit l
        (G.approximateShiftedDefectGraphFamily
          T hInnerSymmetric tau lambdaNet yNet epsilon) := by
    simpa [canonical] using
      G.approximateShiftedDefectGraphFamily_canonical_mem_kuratowskiLowerLimit_of_recovery
        T hP hInnerSymmetric hSelf l hlambda v hv hMem
  simpa [canonical] using
    FilterSet.kuratowskiLimits_eq_singleton_of_outer_subset_of_mem_lower
      l (G.approximateShiftedDefectGraphFamily
        T hInnerSymmetric tau lambdaNet yNet epsilon) canonical hOuter hLower

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
