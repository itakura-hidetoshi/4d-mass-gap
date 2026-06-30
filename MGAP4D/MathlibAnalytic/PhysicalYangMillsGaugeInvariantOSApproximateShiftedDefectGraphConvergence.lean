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

/-- The distance from an arbitrary vector to the canonical bounded resolvent
solution is controlled by the residual of its shifted defect equation. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefect_approximateShift_error_norm_le
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    {lambda : ℝ}
    (hlambda : lambda < G.mass / 2)
    (y u : P.VacuumOrthogonalHilbert) :
    ‖u - G.admissibleRescaledDefectResolvent
          hInnerSymmetric tau hlambda y‖ ≤
      (G.mass / 2 - lambda)⁻¹ *
        ‖T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
              hInnerSymmetric tau.1 u -
            lambda • u - y‖ := by
  let R := G.admissibleRescaledDefectResolvent hInnerSymmetric tau hlambda
  have hInverse :
      R
          (T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
              hInnerSymmetric tau.1 u -
            lambda • u) = u :=
    G.admissibleRescaledDefectResolvent_apply_shift
      T hInnerSymmetric tau hlambda u
  calc
    ‖u - R y‖ =
        ‖R
              (T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
                  hInnerSymmetric tau.1 u -
                lambda • u) -
            R y‖ := by rw [hInverse]
    _ = ‖R
          ((T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
                hInnerSymmetric tau.1 u -
              lambda • u) - y)‖ := by
      exact congrArg
        (fun z : P.VacuumOrthogonalHilbert => ‖z‖)
        (R.map_sub
          (T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
              hInnerSymmetric tau.1 u -
            lambda • u)
          y).symm
    _ ≤ (G.mass / 2 - lambda)⁻¹ *
          ‖T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
                hInnerSymmetric tau.1 u -
              lambda • u - y‖ := by
      simpa [R] using
        realHilbert_uniformCoerciveSymmetricStrongLimit_limitResolvent_norm_bound
          (G.admissibleRescaledDefectData hInnerSymmetric tau)
          hlambda
          ((T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
                hInnerSymmetric tau.1 u -
              lambda • u) - y)

/-- Vanishing residuals for one fixed shifted equation force arbitrary
admissible defect vectors to converge to the canonical continuum resolvent. -/
theorem VacuumSemigroupGapSlope.approximateShiftedAdmissibleRescaledDefect_tendsto_continuumResolvent
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
    Tendsto u atTop
      (nhds
        (G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf hlambda y)) := by
  have hResidualNorm := hResidual.norm
  have hMajorant :
      Tendsto
        (fun n =>
          (G.mass / 2 - lambda)⁻¹ *
            ‖T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
                  hInnerSymmetric (tau n).1 (u n) -
                lambda • u n - y‖)
        atTop
        (nhds 0) := by
    simpa using tendsto_const_nhds.mul hResidualNorm
  have hError :
      Tendsto
        (fun n =>
          u n -
            G.admissibleRescaledDefectResolvent
              hInnerSymmetric (tau n) hlambda y)
        atTop
        (nhds 0) :=
    squeeze_zero_norm'
      (Eventually.of_forall fun n =>
        G.admissibleRescaledDefect_approximateShift_error_norm_le
          T hInnerSymmetric (tau n) hlambda y (u n))
      hMajorant
  have hSelected :=
    (G.admissibleRescaledDefectResolvent_tendsto_continuumResolvent
      T hP hInnerSymmetric hSelf hlambda y).comp hTau
  have hSum := hError.add hSelected
  simpa using hSum

/-- Under the same vanishing-residual hypothesis, the defect values converge to
the closed continuum Hamiltonian value of the resolvent-selected limit. -/
theorem VacuumSemigroupGapSlope.approximateShiftedAdmissibleRescaledDefect_apply_tendsto_continuumHamiltonian
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
        T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
          hInnerSymmetric (tau n).1 (u n))
      atTop
      (nhds
        (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
          (G.vacuumOrthogonalContinuumRealResolventDomainPoint
            T hP hInnerSymmetric hSelf hlambda y))) := by
  have hu :=
    G.approximateShiftedAdmissibleRescaledDefect_tendsto_continuumResolvent
      T hP hInnerSymmetric hSelf hlambda y hTau hResidual
  have hScaled :
      Tendsto
        (fun n => lambda • u n)
        atTop
        (nhds
          (lambda •
            G.vacuumOrthogonalContinuumRealResolvent
              T hP hInnerSymmetric hSelf hlambda y)) :=
    tendsto_const_nhds.smul hu
  have hRight :=
    (hResidual.add hScaled).add
      (tendsto_const_nhds : Tendsto
        (fun _ : ℕ => y) atTop (nhds y))
  have hDefectFunction :
      (fun n =>
        T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
          hInnerSymmetric (tau n).1 (u n)) =
      (fun n =>
        (T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
              hInnerSymmetric (tau n).1 (u n) -
            lambda • u n - y) +
          lambda • u n + y) := by
    funext n
    abel
  rw [hDefectFunction]
  rw [G.vacuumOrthogonalClosedRightHamiltonian_apply_continuumResolventDomainPoint_eq
    T hP hInnerSymmetric hSelf hlambda y]
  simpa [add_comm, add_left_comm, add_assoc] using hRight

/-- Approximate shifted solutions with vanishing residuals converge in the full
product graph topology to the canonical continuum Hamiltonian graph point. -/
theorem VacuumSemigroupGapSlope.approximateShiftedAdmissibleRescaledDefect_graph_tendsto
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
              T hP hInnerSymmetric hSelf hlambda y))) :=
  (G.approximateShiftedAdmissibleRescaledDefect_tendsto_continuumResolvent
      T hP hInnerSymmetric hSelf hlambda y hTau hResidual).prodMk_nhds
    (G.approximateShiftedAdmissibleRescaledDefect_apply_tendsto_continuumHamiltonian
      T hP hInnerSymmetric hSelf hlambda y hTau hResidual)

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
