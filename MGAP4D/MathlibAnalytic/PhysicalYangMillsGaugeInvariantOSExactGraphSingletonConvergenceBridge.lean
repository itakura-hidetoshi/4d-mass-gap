import MGAP4D.MathlibAnalytic.FilterKuratowskiSingletonConvergence
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

/-- The exact shifted-defect graph Kuratowski convergence follows directly
from eventual singleton identification and convergence of the total graph-point net. -/
theorem VacuumSemigroupGapSlope.exactShiftedDefectGraphFamily_kuratowskiLimits_eq_singleton_via_totalGraphPoint
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {ι : Type*} (l : Filter ι) [NeBot l]
    {lambdaNet : ι → ℝ} {lambda : ℝ}
    (hlambda : lambda < G.mass / 2)
    {yNet : ι → P.VacuumOrthogonalHilbert}
    {y : P.VacuumOrthogonalHilbert}
    {tau : ι → G.AdmissibleRescaledDefectTime}
    (hTau : Tendsto tau l G.admissibleRescaledDefectTimeFilter)
    (hLambda : Tendsto lambdaNet l (nhds lambda))
    (hy : Tendsto yNet l (nhds y)) :
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
            T hP hInnerSymmetric hSelf hlambda y))} := by
  let z : ι → P.VacuumOrthogonalHilbert × P.VacuumOrthogonalHilbert :=
    G.totalVaryingShiftResolventGraphPoint
      T hInnerSymmetric tau lambdaNet yNet
  let zStar : P.VacuumOrthogonalHilbert × P.VacuumOrthogonalHilbert :=
    (G.vacuumOrthogonalContinuumRealResolvent
        T hP hInnerSymmetric hSelf hlambda y,
      T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
        (G.vacuumOrthogonalContinuumRealResolventDomainPoint
          T hP hInnerSymmetric hSelf hlambda y))
  have hz : Tendsto z l (nhds zStar) := by
    simpa [z, zStar] using
      G.totalVaryingShiftResolventGraphPoint_tendsto_continuum
        T hP hInnerSymmetric hSelf l hlambda hTau hLambda hy
  have hFamily :
      G.exactShiftedDefectGraphFamily
          T hInnerSymmetric tau lambdaNet yNet =ᶠ[l]
        (fun i => {z i}) := by
    simpa [z] using
      G.exactShiftedDefectGraphFamily_eventually_eq_singleton_totalGraphPoint
        T hInnerSymmetric l hLambda hlambda
  have hSingleton := FilterSet.kuratowskiLimits_singleton_of_tendsto l hz
  have hInnerCongr :=
    FilterSet.kuratowskiInnerLimit_congr_of_eventuallyEq hFamily
  have hOuterCongr :=
    FilterSet.kuratowskiOuterLimit_congr_of_eventuallyEq hFamily
  constructor
  · calc
      FilterSet.kuratowskiInnerLimit l
          (G.exactShiftedDefectGraphFamily
            T hInnerSymmetric tau lambdaNet yNet) =
        FilterSet.kuratowskiInnerLimit l (fun i => {z i}) := hInnerCongr
      _ = {zStar} := hSingleton.1
      _ = {(G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf hlambda y,
        T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
          (G.vacuumOrthogonalContinuumRealResolventDomainPoint
            T hP hInnerSymmetric hSelf hlambda y))} := by rfl
  · calc
      FilterSet.kuratowskiOuterLimit l
          (G.exactShiftedDefectGraphFamily
            T hInnerSymmetric tau lambdaNet yNet) =
        FilterSet.kuratowskiOuterLimit l (fun i => {z i}) := hOuterCongr
      _ = {zStar} := hSingleton.2
      _ = {(G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf hlambda y,
        T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
          (G.vacuumOrthogonalContinuumRealResolventDomainPoint
            T hP hInnerSymmetric hSelf hlambda y))} := by rfl

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
