import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSKuratowskiDefectGraphConvergence
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSFullStrongGraphResolvent
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

/-- Eventual nonnegativity of the residual tolerance makes the approximate
shifted-defect graph family eventually nonempty. -/
theorem VacuumSemigroupGapSlope.approximateShiftedDefectGraphFamily_eventually_nonempty_of_eventually_nonneg
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {ι : Type*} (l : Filter ι) {lambdaNet : ι → ℝ} {lambda : ℝ}
    (hlambda : lambda < G.mass / 2) {yNet : ι → P.VacuumOrthogonalHilbert}
    {tau : ι → G.AdmissibleRescaledDefectTime} {epsilon : ι → ℝ}
    (hLambda : Tendsto lambdaNet l (nhds lambda))
    (hEpsilonNonneg : ∀ᶠ i in l, 0 ≤ epsilon i) :
    ∀ᶠ i in l,
      (G.approximateShiftedDefectGraphFamily
        T hInnerSymmetric tau lambdaNet yNet epsilon i).Nonempty := by
  have hLambdaGap : ∀ᶠ i in l, lambdaNet i < G.mass / 2 :=
    hLambda.eventually (Iio_mem_nhds hlambda)
  filter_upwards [hLambdaGap, hEpsilonNonneg] with i hLambdaI hEpsilonI
  let u := G.admissibleRescaledDefectResolvent
    hInnerSymmetric (tau i) hLambdaI (yNet i)
  refine ⟨(u, T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
    hInnerSymmetric (tau i).1 u), ?_⟩
  change
    T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
        hInnerSymmetric (tau i).1 u =
      T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
        hInnerSymmetric (tau i).1 u ∧
      ‖T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
          hInnerSymmetric (tau i).1 u - lambdaNet i • u - yNet i‖ ≤ epsilon i
  refine ⟨rfl, ?_⟩
  have hEquation :=
    G.vacuumOrthogonalRescaledDefect_apply_admissibleResolvent_eq
      T hInnerSymmetric (tau i) hLambdaI (yNet i)
  have hResidual :
      T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
          hInnerSymmetric (tau i).1 u - lambdaNet i • u - yNet i = 0 := by
    change
      T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
          hInnerSymmetric (tau i).1
          (G.admissibleRescaledDefectResolvent
            hInnerSymmetric (tau i) hLambdaI (yNet i)) -
        lambdaNet i •
          G.admissibleRescaledDefectResolvent
            hInnerSymmetric (tau i) hLambdaI (yNet i) - yNet i = 0
    rw [hEquation]
    abel
  rw [hResidual, norm_zero]
  exact hEpsilonI

/-- Nonnegative tolerances remove the separate eventual-nonemptiness hypothesis
from the Painlevé–Kuratowski convergence theorem. -/
theorem VacuumSemigroupGapSlope.approximateShiftedDefectGraphFamily_kuratowskiLimits_eq_singleton_of_eventually_nonneg
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) {ι : Type*} (l : Filter ι)
    [NeBot l] {lambdaNet : ι → ℝ} {lambda : ℝ} (hlambda : lambda < G.mass / 2)
    {yNet : ι → P.VacuumOrthogonalHilbert} {y : P.VacuumOrthogonalHilbert}
    {tau : ι → G.AdmissibleRescaledDefectTime} {epsilon : ι → ℝ}
    (hTau : Tendsto tau l G.admissibleRescaledDefectTimeFilter)
    (hLambda : Tendsto lambdaNet l (nhds lambda)) (hy : Tendsto yNet l (nhds y))
    (hEpsilon : Tendsto epsilon l (nhds 0))
    (hEpsilonNonneg : ∀ᶠ i in l, 0 ≤ epsilon i) :
    FilterSet.kuratowskiInnerLimit l
        (G.approximateShiftedDefectGraphFamily
          T hInnerSymmetric tau lambdaNet yNet epsilon) =
      {(G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf hlambda y,
        T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
          (G.vacuumOrthogonalContinuumRealResolventDomainPoint
            T hP hInnerSymmetric hSelf hlambda y))} ∧
    FilterSet.kuratowskiOuterLimit l
        (G.approximateShiftedDefectGraphFamily
          T hInnerSymmetric tau lambdaNet yNet epsilon) =
      {(G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf hlambda y,
        T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
          (G.vacuumOrthogonalContinuumRealResolventDomainPoint
            T hP hInnerSymmetric hSelf hlambda y))} := by
  apply G.approximateShiftedDefectGraphFamily_kuratowskiLimits_eq_singleton
    T hP hInnerSymmetric hSelf l hlambda hTau hLambda hy hEpsilon
  exact G.approximateShiftedDefectGraphFamily_eventually_nonempty_of_eventually_nonneg
    T hInnerSymmetric l hlambda hLambda hEpsilonNonneg

/-- In particular, the exact shifted-defect graph family with zero residual
tolerance converges in the Painlevé–Kuratowski sense to the canonical singleton. -/
theorem VacuumSemigroupGapSlope.zeroToleranceShiftedDefectGraphFamily_kuratowskiLimits_eq_singleton
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) {ι : Type*} (l : Filter ι)
    [NeBot l] {lambdaNet : ι → ℝ} {lambda : ℝ} (hlambda : lambda < G.mass / 2)
    {yNet : ι → P.VacuumOrthogonalHilbert} {y : P.VacuumOrthogonalHilbert}
    {tau : ι → G.AdmissibleRescaledDefectTime}
    (hTau : Tendsto tau l G.admissibleRescaledDefectTimeFilter)
    (hLambda : Tendsto lambdaNet l (nhds lambda)) (hy : Tendsto yNet l (nhds y)) :
    FilterSet.kuratowskiInnerLimit l
        (G.approximateShiftedDefectGraphFamily
          T hInnerSymmetric tau lambdaNet yNet (fun _ => 0)) =
      {(G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf hlambda y,
        T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
          (G.vacuumOrthogonalContinuumRealResolventDomainPoint
            T hP hInnerSymmetric hSelf hlambda y))} ∧
    FilterSet.kuratowskiOuterLimit l
        (G.approximateShiftedDefectGraphFamily
          T hInnerSymmetric tau lambdaNet yNet (fun _ => 0)) =
      {(G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf hlambda y,
        T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
          (G.vacuumOrthogonalContinuumRealResolventDomainPoint
            T hP hInnerSymmetric hSelf hlambda y))} := by
  apply G.approximateShiftedDefectGraphFamily_kuratowskiLimits_eq_singleton_of_eventually_nonneg
    T hP hInnerSymmetric hSelf l hlambda hTau hLambda hy tendsto_const_nhds
  exact Eventually.of_forall fun _ => le_rfl

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
