import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSFilterVaryingShiftRhsDefectGraphLimit
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

/-- Over a nontrivial indexing filter, any preassigned strong graph limit of
varying shifted-defect approximants equals the canonical continuum resolvent
graph point. -/
theorem VacuumSemigroupGapSlope.approximateShiftedAdmissibleRescaledDefect_varyingShiftRhs_filter_graph_limit_eq_continuumResolventGraphPoint
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {ι : Type*} (l : Filter ι) [NeBot l]
    {lambdaNet : ι → ℝ} {lambda : ℝ} (hlambda : lambda < G.mass / 2)
    {yNet : ι → P.VacuumOrthogonalHilbert} {y : P.VacuumOrthogonalHilbert}
    {tau : ι → G.AdmissibleRescaledDefectTime}
    {u : ι → P.VacuumOrthogonalHilbert} {x eta : P.VacuumOrthogonalHilbert}
    (hTau : Tendsto tau l G.admissibleRescaledDefectTimeFilter)
    (hLambda : Tendsto lambdaNet l (nhds lambda))
    (hy : Tendsto yNet l (nhds y))
    (hResidual : Tendsto
      (fun i => T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
        hInnerSymmetric (tau i).1 (u i) - lambdaNet i • u i - yNet i)
      l (nhds 0))
    (hu : Tendsto u l (nhds x))
    (hDefect : Tendsto
      (fun i => T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
        hInnerSymmetric (tau i).1 (u i))
      l (nhds eta)) :
    (x, eta) =
      (G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf hlambda y,
        T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
          (G.vacuumOrthogonalContinuumRealResolventDomainPoint
            T hP hInnerSymmetric hSelf hlambda y)) := by
  have hGiven :
      Tendsto
        (fun i =>
          (u i,
            T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
              hInnerSymmetric (tau i).1 (u i)))
        l
        (nhds (x, eta)) :=
    hu.prodMk_nhds hDefect
  have hCanonical :=
    G.approximateShiftedAdmissibleRescaledDefect_varyingShiftRhs_filter_graph_tendsto_continuumResolventGraphPoint
      T hP hInnerSymmetric hSelf l hlambda hTau hLambda hy hResidual
  exact tendsto_nhds_unique hGiven hCanonical

/-- Hence every such filter limit belongs to the graph of the closed continuum
excitation Hamiltonian. -/
theorem VacuumSemigroupGapSlope.approximateShiftedAdmissibleRescaledDefect_varyingShiftRhs_filter_graph_limit_mem_continuumGraph
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {ι : Type*} (l : Filter ι) [NeBot l]
    {lambdaNet : ι → ℝ} {lambda : ℝ} (hlambda : lambda < G.mass / 2)
    {yNet : ι → P.VacuumOrthogonalHilbert} {y : P.VacuumOrthogonalHilbert}
    {tau : ι → G.AdmissibleRescaledDefectTime}
    {u : ι → P.VacuumOrthogonalHilbert} {x eta : P.VacuumOrthogonalHilbert}
    (hTau : Tendsto tau l G.admissibleRescaledDefectTimeFilter)
    (hLambda : Tendsto lambdaNet l (nhds lambda))
    (hy : Tendsto yNet l (nhds y))
    (hResidual : Tendsto
      (fun i => T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
        hInnerSymmetric (tau i).1 (u i) - lambdaNet i • u i - yNet i)
      l (nhds 0))
    (hu : Tendsto u l (nhds x))
    (hDefect : Tendsto
      (fun i => T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
        hInnerSymmetric (tau i).1 (u i))
      l (nhds eta)) :
    ∃ xDomain :
        (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf).domain,
      (xDomain : P.VacuumOrthogonalHilbert) = x ∧
        T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf xDomain = eta := by
  have hLimit :=
    G.approximateShiftedAdmissibleRescaledDefect_varyingShiftRhs_filter_graph_limit_eq_continuumResolventGraphPoint
      T hP hInnerSymmetric hSelf l hlambda hTau hLambda hy hResidual hu hDefect
  let xDomain :=
    G.vacuumOrthogonalContinuumRealResolventDomainPoint
      T hP hInnerSymmetric hSelf hlambda y
  refine ⟨xDomain, ?_, ?_⟩
  · have hx := congrArg Prod.fst hLimit
    simpa [xDomain] using hx.symm
  · have heta := congrArg Prod.snd hLimit
    simpa [xDomain] using heta.symm

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
