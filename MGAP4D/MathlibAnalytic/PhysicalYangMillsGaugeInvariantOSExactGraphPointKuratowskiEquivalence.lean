import MGAP4D.MathlibAnalytic.FilterKuratowskiSingletonEquivalence
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSTotalVaryingResolventGraphPoint
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

/-- Once the varying shift lies eventually below the half-mass threshold,
convergence of the total finite-time resolvent graph-point net is equivalent to
singleton Painlevé–Kuratowski convergence of the exact shifted-defect graphs. -/
theorem VacuumSemigroupGapSlope.totalVaryingShiftResolventGraphPoint_tendsto_iff_exactGraph_kuratowskiLimits_eq_singleton
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {ι : Type*} (l : Filter ι) [NeBot l]
    {tau : ι → G.AdmissibleRescaledDefectTime}
    {lambdaNet : ι → ℝ} {lambda : ℝ}
    {yNet : ι → P.VacuumOrthogonalHilbert}
    {z : P.VacuumOrthogonalHilbert × P.VacuumOrthogonalHilbert}
    (hLambda : Tendsto lambdaNet l (nhds lambda))
    (hlambda : lambda < G.mass / 2) :
    Tendsto
        (G.totalVaryingShiftResolventGraphPoint
          T hInnerSymmetric tau lambdaNet yNet)
        l (nhds z) ↔
      FilterSet.kuratowskiInnerLimit l
          (G.exactShiftedDefectGraphFamily
            T hInnerSymmetric tau lambdaNet yNet) = {z} ∧
      FilterSet.kuratowskiOuterLimit l
          (G.exactShiftedDefectGraphFamily
            T hInnerSymmetric tau lambdaNet yNet) = {z} := by
  apply FilterSet.tendsto_iff_kuratowskiLimits_eq_singleton_of_eventuallyEq l
  exact G.exactShiftedDefectGraphFamily_eventually_eq_singleton_totalGraphPoint
    T hInnerSymmetric l hLambda hlambda

/-- For the canonical continuum graph point, the existing direct resolvent
convergence theorem and the exact-graph Kuratowski theorem are formally the same
singleton convergence statement. -/
theorem VacuumSemigroupGapSlope.continuumResolventGraphPoint_convergence_equiv_exactGraph_kuratowski
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {ι : Type*} (l : Filter ι) [NeBot l]
    {tau : ι → G.AdmissibleRescaledDefectTime}
    {lambdaNet : ι → ℝ} {lambda : ℝ}
    (hlambda : lambda < G.mass / 2)
    {yNet : ι → P.VacuumOrthogonalHilbert}
    {y : P.VacuumOrthogonalHilbert}
    (hLambda : Tendsto lambdaNet l (nhds lambda)) :
    Tendsto
        (G.totalVaryingShiftResolventGraphPoint
          T hInnerSymmetric tau lambdaNet yNet)
        l
        (nhds
          (G.vacuumOrthogonalContinuumRealResolvent
              T hP hInnerSymmetric hSelf hlambda y,
            T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
              (G.vacuumOrthogonalContinuumRealResolventDomainPoint
                T hP hInnerSymmetric hSelf hlambda y))) ↔
      FilterSet.kuratowskiInnerLimit l
          (G.exactShiftedDefectGraphFamily
            T hInnerSymmetric tau lambdaNet yNet) =
        {(G.vacuumOrthogonalContinuumRealResolvent
            T hP hInnerSymmetric hSelf hlambda y,
          T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
            (G.vacuumOrthogonalContinuumRealResolventDomainPoint
              T hP hInnerSymmetric hSelf hlambda y))} ∧
      FilterSet.kuratowskiOuterLimit l
          (G.exactShiftedDefectGraphFamily
            T hInnerSymmetric tau lambdaNet yNet) =
        {(G.vacuumOrthogonalContinuumRealResolvent
            T hP hInnerSymmetric hSelf hlambda y,
          T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
            (G.vacuumOrthogonalContinuumRealResolventDomainPoint
              T hP hInnerSymmetric hSelf hlambda y))} :=
  G.totalVaryingShiftResolventGraphPoint_tendsto_iff_exactGraph_kuratowskiLimits_eq_singleton
    T hInnerSymmetric l hLambda hlambda

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
