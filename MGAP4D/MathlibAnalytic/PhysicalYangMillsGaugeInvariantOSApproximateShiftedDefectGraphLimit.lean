import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSShiftedDefectGraphLimitIdentification
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

/-- A sequence of admissible rescaled-defect vectors whose shifted-equation
residual tends strongly to zero converges, together with its defect values, to
the canonical continuum resolvent graph point. -/
theorem VacuumSemigroupGapSlope.approximateShiftedAdmissibleRescaledDefect_graph_tendsto_continuumResolventGraphPoint
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
    (hTau : Tendsto tau atTop G.admissibleRescaledDefectTimeFilter)
    (hResidual : Tendsto
      (fun n =>
        T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
              hInnerSymmetric (tau n).1 (u n) -
            lambda • u n - y)
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
  let r : ℕ → P.VacuumOrthogonalHilbert := fun n =>
    T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
          hInnerSymmetric (tau n).1 (u n) -
        lambda • u n - y
  have hr : Tendsto r atTop (nhds 0) := by
    simpa [r] using hResidual
  have hErrorEq (n : ℕ) :
      u n -
          G.admissibleRescaledDefectResolvent
            hInnerSymmetric (tau n) hlambda y =
        G.admissibleRescaledDefectResolvent
          hInnerSymmetric (tau n) hlambda (r n) := by
    let R := G.admissibleRescaledDefectResolvent
      hInnerSymmetric (tau n) hlambda
    have hInverse :
        R
            (T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
                hInnerSymmetric (tau n).1 (u n) -
              lambda • u n) =
          u n :=
      G.admissibleRescaledDefectResolvent_apply_shift
        T hInnerSymmetric (tau n) hlambda (u n)
    calc
      u n - R y =
          R
              (T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
                  hInnerSymmetric (tau n).1 (u n) -
                lambda • u n) - R y := by
            rw [hInverse]
      _ = R
          ((T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
                hInnerSymmetric (tau n).1 (u n) -
              lambda • u n) - y) :=
        (R.map_sub _ _).symm
      _ = R (r n) := by
        rfl
  have hErrorNormLe (n : ℕ) :
      ‖u n -
          G.admissibleRescaledDefectResolvent
            hInnerSymmetric (tau n) hlambda y‖ ≤
        (G.mass / 2 - lambda)⁻¹ * ‖r n‖ := by
    rw [hErrorEq n]
    exact
      realHilbert_uniformCoerciveSymmetricStrongLimit_limitResolvent_norm_bound
        (G.admissibleRescaledDefectData hInnerSymmetric (tau n))
        hlambda
        (r n)
  have hMajorant :
      Tendsto
        (fun n => (G.mass / 2 - lambda)⁻¹ * ‖r n‖)
        atTop
        (nhds 0) := by
    simpa using tendsto_const_nhds.mul hr.norm
  have hError :
      Tendsto
        (fun n =>
          u n -
            G.admissibleRescaledDefectResolvent
              hInnerSymmetric (tau n) hlambda y)
        atTop
        (nhds 0) :=
    squeeze_zero_norm'
      (Eventually.of_forall hErrorNormLe)
      hMajorant
  have hSelected :
      Tendsto
        (fun n =>
          G.admissibleRescaledDefectResolvent
            hInnerSymmetric (tau n) hlambda y)
        atTop
        (nhds
          (G.vacuumOrthogonalContinuumRealResolvent
            T hP hInnerSymmetric hSelf hlambda y)) :=
    (G.admissibleRescaledDefectResolvent_tendsto_continuumResolvent
      T hP hInnerSymmetric hSelf hlambda y).comp hTau
  have hu :
      Tendsto u atTop
        (nhds
          (G.vacuumOrthogonalContinuumRealResolvent
            T hP hInnerSymmetric hSelf hlambda y)) := by
    simpa only [sub_add_cancel, zero_add] using hError.add hSelected
  have hScaled :
      Tendsto
        (fun n => lambda • u n)
        atTop
        (nhds
          (lambda •
            G.vacuumOrthogonalContinuumRealResolvent
              T hP hInnerSymmetric hSelf hlambda y)) :=
    tendsto_const_nhds.smul hu
  have hRight :
      Tendsto
        (fun n => y + lambda • u n)
        atTop
        (nhds
          (y + lambda •
            G.vacuumOrthogonalContinuumRealResolvent
              T hP hInnerSymmetric hSelf hlambda y)) :=
    tendsto_const_nhds.add hScaled
  have hDefectRaw :
      Tendsto
        (fun n => r n + (y + lambda • u n))
        atTop
        (nhds
          (y + lambda •
            G.vacuumOrthogonalContinuumRealResolvent
              T hP hInnerSymmetric hSelf hlambda y)) := by
    simpa only [zero_add] using hr.add hRight
  have hDefectFunction :
      (fun n => r n + (y + lambda • u n)) =
        (fun n =>
          T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
            hInnerSymmetric (tau n).1 (u n)) := by
    funext n
    dsimp [r]
    abel
  rw [hDefectFunction] at hDefectRaw
  have hDefect :
      Tendsto
        (fun n =>
          T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
            hInnerSymmetric (tau n).1 (u n))
        atTop
        (nhds
          (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
            (G.vacuumOrthogonalContinuumRealResolventDomainPoint
              T hP hInnerSymmetric hSelf hlambda y))) := by
    simpa only [
      G.vacuumOrthogonalClosedRightHamiltonian_apply_continuumResolventDomainPoint_eq
        T hP hInnerSymmetric hSelf hlambda y] using hDefectRaw
  exact hu.prodMk_nhds hDefect

/-- Consequently, every preassigned strong graph limit of an asymptotically
shifted rescaled-defect sequence is a graph point of the closed continuum
excitation Hamiltonian. -/
theorem VacuumSemigroupGapSlope.approximateShiftedAdmissibleRescaledDefect_graph_limit_mem_continuumGraph
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
    (hResidual : Tendsto
      (fun n =>
        T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
              hInnerSymmetric (tau n).1 (u n) -
            lambda • u n - y)
      atTop (nhds 0))
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
  have hCanonical :=
    G.approximateShiftedAdmissibleRescaledDefect_graph_tendsto_continuumResolventGraphPoint
      T hP hInnerSymmetric hSelf hlambda y hTau hResidual
  have hGiven :
      Tendsto
        (fun n =>
          (u n,
            T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
              hInnerSymmetric (tau n).1 (u n)))
        atTop
        (nhds (x, eta)) :=
    hu.prodMk_nhds hDefect
  have hLimit := tendsto_nhds_unique hGiven hCanonical
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
