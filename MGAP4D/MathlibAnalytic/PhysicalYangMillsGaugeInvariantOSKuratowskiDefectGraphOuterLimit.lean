import MGAP4D.MathlibAnalytic.FilterKuratowskiOuterLimitSubnet
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSShiftedDefectGraphOuterLimit
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

/-- The full filter Painlevé–Kuratowski outer limit of approximate shifted-defect
graph points is contained in the singleton canonical continuum graph point. -/
theorem VacuumSemigroupGapSlope.approximateShiftedDefectGraphFamily_kuratowskiOuterLimit_subset_singleton
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) {ι : Type*} (l : Filter ι)
    {lambdaNet : ι → ℝ} {lambda : ℝ} (hlambda : lambda < G.mass / 2)
    {yNet : ι → P.VacuumOrthogonalHilbert} {y : P.VacuumOrthogonalHilbert}
    {tau : ι → G.AdmissibleRescaledDefectTime} {epsilon : ι → ℝ}
    (hTau : Tendsto tau l G.admissibleRescaledDefectTimeFilter)
    (hLambda : Tendsto lambdaNet l (nhds lambda)) (hy : Tendsto yNet l (nhds y))
    (hEpsilon : Tendsto epsilon l (nhds 0)) :
    FilterSet.kuratowskiOuterLimit l
      (G.approximateShiftedDefectGraphFamily
        T hInnerSymmetric tau lambdaNet yNet epsilon) ⊆
      {(G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf hlambda y,
        T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
          (G.vacuumOrthogonalContinuumRealResolventDomainPoint
            T hP hInnerSymmetric hSelf hlambda y))} := by
  intro z hz
  have hzConvergent :=
    FilterSet.kuratowskiOuterLimit_subset_convergentSelectionOuterLimit l
      (G.approximateShiftedDefectGraphFamily
        T hInnerSymmetric tau lambdaNet yNet epsilon) hz
  rcases hzConvergent with ⟨p, hp, hIndex, hPoint, hMem⟩
  letI : NeBot p := hp
  let u :
      (ι × (P.VacuumOrthogonalHilbert × P.VacuumOrthogonalHilbert)) →
        P.VacuumOrthogonalHilbert := fun w => w.2.1
  let tau' := fun w : ι ×
      (P.VacuumOrthogonalHilbert × P.VacuumOrthogonalHilbert) => tau w.1
  let lambdaNet' := fun w : ι ×
      (P.VacuumOrthogonalHilbert × P.VacuumOrthogonalHilbert) => lambdaNet w.1
  let yNet' := fun w : ι ×
      (P.VacuumOrthogonalHilbert × P.VacuumOrthogonalHilbert) => yNet w.1
  let epsilon' := fun w : ι ×
      (P.VacuumOrthogonalHilbert × P.VacuumOrthogonalHilbert) => epsilon w.1
  have hTau' : Tendsto tau' p G.admissibleRescaledDefectTimeFilter := by
    simpa [tau'] using hTau.comp hIndex
  have hLambda' : Tendsto lambdaNet' p (nhds lambda) := by
    simpa [lambdaNet'] using hLambda.comp hIndex
  have hy' : Tendsto yNet' p (nhds y) := by
    simpa [yNet'] using hy.comp hIndex
  have hEpsilon' : Tendsto epsilon' p (nhds 0) := by
    simpa [epsilon'] using hEpsilon.comp hIndex
  have hGraphEq :
      (fun w => w.2) =ᶠ[p] fun w =>
        (u w, T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
          hInnerSymmetric (tau' w).1 (u w)) := by
    filter_upwards [hMem] with w hw
    exact Prod.ext rfl (by simpa [u, tau'] using hw.1)
  have hResidualNormLe :
      ∀ᶠ w in p,
        ‖T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
            hInnerSymmetric (tau' w).1 (u w) - lambdaNet' w • u w - yNet' w‖ ≤
          epsilon' w := by
    filter_upwards [hMem] with w hw
    simpa [u, tau', lambdaNet', yNet', epsilon'] using hw.2
  have hResidual :
      Tendsto
        (fun w => T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
          hInnerSymmetric (tau' w).1 (u w) - lambdaNet' w • u w - yNet' w)
        p (nhds 0) :=
    squeeze_zero_norm' hResidualNormLe hEpsilon'
  let canonical : P.VacuumOrthogonalHilbert × P.VacuumOrthogonalHilbert :=
    (G.vacuumOrthogonalContinuumRealResolvent
        T hP hInnerSymmetric hSelf hlambda y,
      T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
        (G.vacuumOrthogonalContinuumRealResolventDomainPoint
          T hP hInnerSymmetric hSelf hlambda y))
  have hCanonical :
      Tendsto
        (fun w =>
          (u w, T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
            hInnerSymmetric (tau' w).1 (u w)))
        p (nhds canonical) := by
    simpa [canonical] using
      G.approximateShiftedAdmissibleRescaledDefect_varyingShiftRhs_filter_graph_tendsto_continuumResolventGraphPoint
        T hP hInnerSymmetric hSelf p hlambda hTau' hLambda' hy' hResidual
  have hSelected : Tendsto (fun w => w.2) p (nhds canonical) :=
    hCanonical.congr' hGraphEq.symm
  have hzCanonical : z = canonical := tendsto_nhds_unique hPoint hSelected
  simpa [canonical] using hzCanonical

/-- Consequently every point in this Kuratowski outer limit belongs to the graph
of the closed continuum excitation Hamiltonian. -/
theorem VacuumSemigroupGapSlope.approximateShiftedDefectGraphFamily_kuratowskiOuterLimit_mem_continuumGraph
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) {ι : Type*} (l : Filter ι)
    {lambdaNet : ι → ℝ} {lambda : ℝ} (hlambda : lambda < G.mass / 2)
    {yNet : ι → P.VacuumOrthogonalHilbert} {y : P.VacuumOrthogonalHilbert}
    {tau : ι → G.AdmissibleRescaledDefectTime} {epsilon : ι → ℝ}
    (hTau : Tendsto tau l G.admissibleRescaledDefectTimeFilter)
    (hLambda : Tendsto lambdaNet l (nhds lambda)) (hy : Tendsto yNet l (nhds y))
    (hEpsilon : Tendsto epsilon l (nhds 0))
    {z : P.VacuumOrthogonalHilbert × P.VacuumOrthogonalHilbert}
    (hz : z ∈ FilterSet.kuratowskiOuterLimit l
      (G.approximateShiftedDefectGraphFamily
        T hInnerSymmetric tau lambdaNet yNet epsilon)) :
    ∃ xDomain :
        (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf).domain,
      (xDomain : P.VacuumOrthogonalHilbert) = z.1 ∧
        T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf xDomain = z.2 := by
  have hzSingleton :=
    G.approximateShiftedDefectGraphFamily_kuratowskiOuterLimit_subset_singleton
      T hP hInnerSymmetric hSelf l hlambda hTau hLambda hy hEpsilon hz
  have hzEq :
      z = (G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf hlambda y,
        T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
          (G.vacuumOrthogonalContinuumRealResolventDomainPoint
            T hP hInnerSymmetric hSelf hlambda y)) := by
    simpa using hzSingleton
  let xDomain :=
    G.vacuumOrthogonalContinuumRealResolventDomainPoint
      T hP hInnerSymmetric hSelf hlambda y
  refine ⟨xDomain, ?_, ?_⟩
  · have hx := congrArg Prod.fst hzEq
    simpa [xDomain] using hx.symm
  · have heta := congrArg Prod.snd hzEq
    simpa [xDomain] using heta.symm

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
