import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSClosedGraphSequentialLimit
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

/-- Any strongly convergent sequence of admissible rescaled-defect solutions of
one fixed shifted equation has the canonical continuum resolvent graph point as
its unique graph limit. -/
theorem VacuumSemigroupGapSlope.shiftedAdmissibleRescaledDefect_graph_limit_eq_continuumResolventGraphPoint
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ}
    (hlambda : lambda < G.mass / 2)
    (y : P.VacuumOrthogonalHilbert)
    {tau : ℕ → G.AdmissibleRescaledDefectTime}
    {u : ℕ → P.VacuumOrthogonalHilbert}
    {x eta : P.VacuumOrthogonalHilbert}
    (hTau : Tendsto tau atTop G.admissibleRescaledDefectTimeFilter)
    (hShift : ∀ n,
      T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
          hInnerSymmetric (tau n).1 (u n) =
        y + lambda • u n)
    (hu : Tendsto u atTop (nhds x))
    (hDefect : Tendsto
      (fun n =>
        T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
          hInnerSymmetric (tau n).1 (u n))
      atTop (nhds eta)) :
    (x, eta) =
      (G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf hlambda y,
        T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
          (G.vacuumOrthogonalContinuumRealResolventDomainPoint
            T hP hInnerSymmetric hSelf hlambda y)) := by
  have huSelected (n : ℕ) :
      u n =
        G.admissibleRescaledDefectResolvent
          hInnerSymmetric (tau n) hlambda y := by
    have hInverse :=
      G.admissibleRescaledDefectResolvent_apply_shift
        T hInnerSymmetric (tau n) hlambda (u n)
    have hShift' :
        T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
            hInnerSymmetric (tau n).1 (u n) -
          lambda • u n = y := by
      rw [hShift n]
      abel
    rw [hShift'] at hInverse
    exact hInverse.symm
  have hArbitraryPair :
      Tendsto
        (fun n =>
          (u n,
            T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
              hInnerSymmetric (tau n).1 (u n)))
        atTop
        (nhds (x, eta)) :=
    hu.prodMk_nhds hDefect
  have hSelectedPair :=
    (G.admissibleRescaledDefect_resolvent_graph_tendsto
      T hP hInnerSymmetric hSelf hlambda y).comp hTau
  have hPairFunctions :
      (fun n =>
        (u n,
          T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
            hInnerSymmetric (tau n).1 (u n))) =
      (fun n =>
        (G.admissibleRescaledDefectResolvent
            hInnerSymmetric (tau n) hlambda y,
          T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
            hInnerSymmetric (tau n).1
            (G.admissibleRescaledDefectResolvent
              hInnerSymmetric (tau n) hlambda y))) := by
    funext n
    rw [huSelected n]
  rw [hPairFunctions] at hArbitraryPair
  exact tendsto_nhds_unique hArbitraryPair hSelectedPair

/-- In particular, every such convergent shifted-defect graph sequence has a
limit in the graph of the closed continuum excitation Hamiltonian. -/
theorem VacuumSemigroupGapSlope.shiftedAdmissibleRescaledDefect_graph_limit_mem_continuumGraph
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ}
    (hlambda : lambda < G.mass / 2)
    (y : P.VacuumOrthogonalHilbert)
    {tau : ℕ → G.AdmissibleRescaledDefectTime}
    {u : ℕ → P.VacuumOrthogonalHilbert}
    {x eta : P.VacuumOrthogonalHilbert}
    (hTau : Tendsto tau atTop G.admissibleRescaledDefectTimeFilter)
    (hShift : ∀ n,
      T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
          hInnerSymmetric (tau n).1 (u n) =
        y + lambda • u n)
    (hu : Tendsto u atTop (nhds x))
    (hDefect : Tendsto
      (fun n =>
        T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
          hInnerSymmetric (tau n).1 (u n))
      atTop (nhds eta)) :
    ∃ xDomain :
        (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf).domain,
      (xDomain : P.VacuumOrthogonalHilbert) = x ∧
        T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf xDomain = eta := by
  have hLimit :=
    G.shiftedAdmissibleRescaledDefect_graph_limit_eq_continuumResolventGraphPoint
      T hP hInnerSymmetric hSelf hlambda y hTau hShift hu hDefect
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
