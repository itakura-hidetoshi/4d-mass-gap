import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVaryingRhsDefectGraphLimit
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

/-- Approximate shifted equations with simultaneously varying shifts and
right-hand sides converge in graph norm once the approximate vectors are
uniformly bounded. -/
theorem VacuumSemigroupGapSlope.approximateShiftedAdmissibleRescaledDefect_varyingShiftRhs_bounded_graph_tendsto_continuumResolventGraphPoint
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambdaSeq : ℕ → ℝ}
    {lambda : ℝ}
    (hlambda : lambda < G.mass / 2)
    {ySeq : ℕ → P.VacuumOrthogonalHilbert}
    {y : P.VacuumOrthogonalHilbert}
    {tau : ℕ → G.AdmissibleRescaledDefectTime}
    {u : ℕ → P.VacuumOrthogonalHilbert}
    (hTau : Tendsto tau atTop G.admissibleRescaledDefectTimeFilter)
    (hLambda : Tendsto lambdaSeq atTop (nhds lambda))
    (hy : Tendsto ySeq atTop (nhds y))
    (hBound : ∃ C : ℝ, ∀ n, ‖u n‖ ≤ C)
    (hResidual : Tendsto
      (fun n => T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
          hInnerSymmetric (tau n).1 (u n) - lambdaSeq n • u n - ySeq n)
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
  obtain ⟨C, hC⟩ := hBound
  have hLambdaError :
      Tendsto (fun n => lambdaSeq n - lambda) atTop (nhds 0) := by
    simpa using hLambda.sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => lambda) atTop (nhds lambda))
  have hShiftNormLe (n : ℕ) :
      ‖lambdaSeq n • u n - lambda • u n‖ ≤
        ‖lambdaSeq n - lambda‖ * C := by
    rw [← sub_smul, norm_smul]
    exact mul_le_mul_of_nonneg_left (hC n) (norm_nonneg _)
  have hShiftMajorant :
      Tendsto (fun n => ‖lambdaSeq n - lambda‖ * C) atTop (nhds 0) := by
    have hConstC :
        Tendsto (fun _ : ℕ => C) atTop (nhds C) := tendsto_const_nhds
    simpa using hLambdaError.norm.mul hConstC
  have hShiftError :
      Tendsto
        (fun n => lambdaSeq n • u n - lambda • u n)
        atTop
        (nhds 0) :=
    squeeze_zero_norm'
      (Eventually.of_forall hShiftNormLe)
      hShiftMajorant
  have hResidualFixedRaw :
      Tendsto
        (fun n =>
          (T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
                hInnerSymmetric (tau n).1 (u n) -
              lambdaSeq n • u n - ySeq n) +
            (lambdaSeq n • u n - lambda • u n))
        atTop
        (nhds 0) := by
    simpa using hResidual.add hShiftError
  have hResidualFunction :
      (fun n =>
        (T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
              hInnerSymmetric (tau n).1 (u n) -
            lambdaSeq n • u n - ySeq n) +
          (lambdaSeq n • u n - lambda • u n)) =
      (fun n =>
        T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
              hInnerSymmetric (tau n).1 (u n) -
            lambda • u n - ySeq n) := by
    funext n
    abel
  rw [hResidualFunction] at hResidualFixedRaw
  exact
    G.approximateShiftedAdmissibleRescaledDefect_varyingRhs_graph_tendsto_continuumResolventGraphPoint
      T hP hInnerSymmetric hSelf hlambda hTau hy hResidualFixedRaw

/-- Any preassigned strong graph limit of approximate equations with convergent
shifts and right-hand sides lies in the graph of the closed continuum
excitation Hamiltonian. -/
theorem VacuumSemigroupGapSlope.approximateShiftedAdmissibleRescaledDefect_varyingShiftRhs_graph_limit_mem_continuumGraph
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambdaSeq : ℕ → ℝ}
    {lambda : ℝ}
    (hlambda : lambda < G.mass / 2)
    {ySeq : ℕ → P.VacuumOrthogonalHilbert}
    {y : P.VacuumOrthogonalHilbert}
    {tau : ℕ → G.AdmissibleRescaledDefectTime}
    {u : ℕ → P.VacuumOrthogonalHilbert}
    {x eta : P.VacuumOrthogonalHilbert}
    (hTau : Tendsto tau atTop G.admissibleRescaledDefectTimeFilter)
    (hLambda : Tendsto lambdaSeq atTop (nhds lambda))
    (hy : Tendsto ySeq atTop (nhds y))
    (hResidual : Tendsto
      (fun n => T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
          hInnerSymmetric (tau n).1 (u n) - lambdaSeq n • u n - ySeq n)
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
  have hVariableScaled :
      Tendsto (fun n => lambdaSeq n • u n) atTop (nhds (lambda • x)) :=
    hLambda.smul hu
  have hFixedScaled :
      Tendsto (fun n => lambda • u n) atTop (nhds (lambda • x)) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => lambda) atTop (nhds lambda)).smul hu
  have hShiftError :
      Tendsto
        (fun n => lambdaSeq n • u n - lambda • u n)
        atTop
        (nhds 0) := by
    simpa using hVariableScaled.sub hFixedScaled
  have hResidualFixedRaw :
      Tendsto
        (fun n =>
          (T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
                hInnerSymmetric (tau n).1 (u n) -
              lambdaSeq n • u n - ySeq n) +
            (lambdaSeq n • u n - lambda • u n))
        atTop
        (nhds 0) := by
    simpa using hResidual.add hShiftError
  have hResidualFunction :
      (fun n =>
        (T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
              hInnerSymmetric (tau n).1 (u n) -
            lambdaSeq n • u n - ySeq n) +
          (lambdaSeq n • u n - lambda • u n)) =
      (fun n =>
        T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
              hInnerSymmetric (tau n).1 (u n) -
            lambda • u n - ySeq n) := by
    funext n
    abel
  rw [hResidualFunction] at hResidualFixedRaw
  exact
    G.approximateShiftedAdmissibleRescaledDefect_varyingRhs_graph_limit_mem_continuumGraph
      T hP hInnerSymmetric hSelf hlambda
      hTau hy hResidualFixedRaw hu hDefect

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
