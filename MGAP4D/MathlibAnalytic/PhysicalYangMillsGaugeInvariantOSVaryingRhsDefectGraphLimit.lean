import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximateShiftedDefectGraphLimit
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

/-- Approximate shifted equations remain graph-convergent when their right-hand
sides vary strongly toward a limiting excitation vector. -/
theorem VacuumSemigroupGapSlope.approximateShiftedAdmissibleRescaledDefect_varyingRhs_graph_tendsto_continuumResolventGraphPoint
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ}
    (hlambda : lambda < G.mass / 2)
    {ySeq : ℕ → P.VacuumOrthogonalHilbert}
    {y : P.VacuumOrthogonalHilbert}
    {tau : ℕ → G.AdmissibleRescaledDefectTime}
    {u : ℕ → P.VacuumOrthogonalHilbert}
    (hTau : Tendsto tau atTop G.admissibleRescaledDefectTimeFilter)
    (hy : Tendsto ySeq atTop (nhds y))
    (hResidual : Tendsto
      (fun n => T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
          hInnerSymmetric (tau n).1 (u n) - lambda • u n - ySeq n)
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        (u n,
          T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
            hInnerSymmetric (tau n).1 (u n)))
      atTop
      (nhds
        (G.vacuumOrthogonalContinuumRealResolvent
            T hP hInnerSymmetric hSelf hlambda y,
          T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
            (G.vacuumOrthogonalContinuumRealResolventDomainPoint
              T hP hInnerSymmetric hSelf hlambda y))) := by
  have hYError :
      Tendsto (fun n => ySeq n - y) atTop (nhds 0) := by
    simpa using hy.sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => y) atTop (nhds y))
  have hResidualFixedRaw :
      Tendsto
        (fun n =>
          (T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
                hInnerSymmetric (tau n).1 (u n) -
              lambda • u n - ySeq n) +
            (ySeq n - y))
        atTop
        (nhds 0) := by
    simpa only [zero_add] using hResidual.add hYError
  have hResidualFunction :
      (fun n =>
        (T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
              hInnerSymmetric (tau n).1 (u n) -
            lambda • u n - ySeq n) +
          (ySeq n - y)) =
      (fun n =>
        T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
              hInnerSymmetric (tau n).1 (u n) -
            lambda • u n - y) := by
    funext n
    abel
  rw [hResidualFunction] at hResidualFixedRaw
  exact
    G.approximateShiftedAdmissibleRescaledDefect_graph_tendsto_continuumResolventGraphPoint
      T hP hInnerSymmetric hSelf hlambda y hTau hResidualFixedRaw

/-- Any preassigned strong graph limit of approximate shifted equations with
convergent right-hand sides lies in the graph of the closed continuum
excitation Hamiltonian. -/
theorem VacuumSemigroupGapSlope.approximateShiftedAdmissibleRescaledDefect_varyingRhs_graph_limit_mem_continuumGraph
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ}
    (hlambda : lambda < G.mass / 2)
    {ySeq : ℕ → P.VacuumOrthogonalHilbert}
    {y : P.VacuumOrthogonalHilbert}
    {tau : ℕ → G.AdmissibleRescaledDefectTime}
    {u : ℕ → P.VacuumOrthogonalHilbert}
    {x eta : P.VacuumOrthogonalHilbert}
    (hTau : Tendsto tau atTop G.admissibleRescaledDefectTimeFilter)
    (hy : Tendsto ySeq atTop (nhds y))
    (hResidual : Tendsto
      (fun n => T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
          hInnerSymmetric (tau n).1 (u n) - lambda • u n - ySeq n)
      atTop (nhds 0))
    (hu : Tendsto u atTop (nhds x))
    (hDefect : Tendsto
      (fun n => T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
          hInnerSymmetric (tau n).1 (u n))
      atTop (nhds eta)) :
    ∃ xDomain :
        (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf).domain,
      (xDomain : P.VacuumOrthogonalHilbert) = x ∧
        T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf xDomain = eta := by
  have hYError :
      Tendsto (fun n => ySeq n - y) atTop (nhds 0) := by
    simpa using hy.sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => y) atTop (nhds y))
  have hResidualFixedRaw :
      Tendsto
        (fun n =>
          (T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
                hInnerSymmetric (tau n).1 (u n) -
              lambda • u n - ySeq n) +
            (ySeq n - y))
        atTop
        (nhds 0) := by
    simpa only [zero_add] using hResidual.add hYError
  have hResidualFunction :
      (fun n =>
        (T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
              hInnerSymmetric (tau n).1 (u n) -
            lambda • u n - ySeq n) +
          (ySeq n - y)) =
      (fun n =>
        T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
              hInnerSymmetric (tau n).1 (u n) -
            lambda • u n - y) := by
    funext n
    abel
  rw [hResidualFunction] at hResidualFixedRaw
  exact
    G.approximateShiftedAdmissibleRescaledDefect_graph_limit_mem_continuumGraph
      T hP hInnerSymmetric hSelf hlambda y
      hTau hResidualFixedRaw hu hDefect

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
