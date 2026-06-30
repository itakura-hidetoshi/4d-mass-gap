import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSExactShiftedDefectGraphSingleton
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

/-- A totalized varying-shift finite-time resolvent vector.  Below the half-mass
threshold it is the genuine resolvent solution; outside that region it is zero. -/
noncomputable def VacuumSemigroupGapSlope.totalVaryingShiftResolventVector
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {ι : Type*} (tau : ι → G.AdmissibleRescaledDefectTime)
    (lambdaNet : ι → ℝ) (yNet : ι → P.VacuumOrthogonalHilbert)
    (i : ι) : P.VacuumOrthogonalHilbert :=
  if h : lambdaNet i < G.mass / 2 then
    G.admissibleRescaledDefectResolvent
      hInnerSymmetric (tau i) h (yNet i)
  else 0

/-- The product graph point associated with the totalized varying-shift
finite-time resolvent vector. -/
noncomputable def VacuumSemigroupGapSlope.totalVaryingShiftResolventGraphPoint
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {ι : Type*} (tau : ι → G.AdmissibleRescaledDefectTime)
    (lambdaNet : ι → ℝ) (yNet : ι → P.VacuumOrthogonalHilbert)
    (i : ι) : P.VacuumOrthogonalHilbert × P.VacuumOrthogonalHilbert :=
  (G.totalVaryingShiftResolventVector
      T hInnerSymmetric tau lambdaNet yNet i,
    T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
      hInnerSymmetric (tau i).1
      (G.totalVaryingShiftResolventVector
        T hInnerSymmetric tau lambdaNet yNet i))

@[simp]
theorem VacuumSemigroupGapSlope.totalVaryingShiftResolventVector_of_lt
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {ι : Type*} (tau : ι → G.AdmissibleRescaledDefectTime)
    (lambdaNet : ι → ℝ) (yNet : ι → P.VacuumOrthogonalHilbert)
    (i : ι) (hLambdaI : lambdaNet i < G.mass / 2) :
    G.totalVaryingShiftResolventVector
        T hInnerSymmetric tau lambdaNet yNet i =
      G.admissibleRescaledDefectResolvent
        hInnerSymmetric (tau i) hLambdaI (yNet i) := by
  simp [VacuumSemigroupGapSlope.totalVaryingShiftResolventVector, hLambdaI]

/-- A convergent shift net below the limiting half-mass threshold makes the
exact graph family eventually equal to singletons of one total graph-point net. -/
theorem VacuumSemigroupGapSlope.exactShiftedDefectGraphFamily_eventually_eq_singleton_totalGraphPoint
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {ι : Type*} (l : Filter ι)
    {tau : ι → G.AdmissibleRescaledDefectTime}
    {lambdaNet : ι → ℝ} {lambda : ℝ}
    {yNet : ι → P.VacuumOrthogonalHilbert}
    (hLambda : Tendsto lambdaNet l (nhds lambda))
    (hlambda : lambda < G.mass / 2) :
    ∀ᶠ i in l,
      G.exactShiftedDefectGraphFamily
          T hInnerSymmetric tau lambdaNet yNet i =
        {G.totalVaryingShiftResolventGraphPoint
          T hInnerSymmetric tau lambdaNet yNet i} := by
  have hGap : ∀ᶠ i in l, lambdaNet i < G.mass / 2 :=
    hLambda.eventually (Iio_mem_nhds hlambda)
  filter_upwards [hGap] with i hLambdaI
  rw [G.exactShiftedDefectGraphFamily_eq_singleton_resolventGraphPoint
    T hInnerSymmetric tau lambdaNet yNet i hLambdaI]
  congr 1
  apply Prod.ext
  · symm
    exact G.totalVaryingShiftResolventVector_of_lt
      T hInnerSymmetric tau lambdaNet yNet i hLambdaI
  · rw [VacuumSemigroupGapSlope.totalVaryingShiftResolventGraphPoint]
    rw [G.totalVaryingShiftResolventVector_of_lt
      T hInnerSymmetric tau lambdaNet yNet i hLambdaI]

/-- The totalized varying finite-time resolvent graph point converges directly
to the canonical continuum resolvent graph point. -/
theorem VacuumSemigroupGapSlope.totalVaryingShiftResolventGraphPoint_tendsto_continuum
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {ι : Type*} (l : Filter ι)
    {tau : ι → G.AdmissibleRescaledDefectTime}
    {lambdaNet : ι → ℝ} {lambda : ℝ}
    (hlambda : lambda < G.mass / 2)
    {yNet : ι → P.VacuumOrthogonalHilbert}
    {y : P.VacuumOrthogonalHilbert}
    (hTau : Tendsto tau l G.admissibleRescaledDefectTimeFilter)
    (hLambda : Tendsto lambdaNet l (nhds lambda))
    (hy : Tendsto yNet l (nhds y)) :
    Tendsto
      (G.totalVaryingShiftResolventGraphPoint
        T hInnerSymmetric tau lambdaNet yNet)
      l
      (nhds
        (G.vacuumOrthogonalContinuumRealResolvent
            T hP hInnerSymmetric hSelf hlambda y,
          T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
            (G.vacuumOrthogonalContinuumRealResolventDomainPoint
              T hP hInnerSymmetric hSelf hlambda y))) := by
  let u : ι → P.VacuumOrthogonalHilbert := fun i =>
    G.totalVaryingShiftResolventVector
      T hInnerSymmetric tau lambdaNet yNet i
  have hGap : ∀ᶠ i in l, lambdaNet i < G.mass / 2 :=
    hLambda.eventually (Iio_mem_nhds hlambda)
  have hResidualEventually :
      ∀ᶠ i in l,
        T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
            hInnerSymmetric (tau i).1 (u i) - lambdaNet i • u i - yNet i = 0 := by
    filter_upwards [hGap] with i hLambdaI
    have hEquation :=
      G.vacuumOrthogonalRescaledDefect_apply_admissibleResolvent_eq
        T hInnerSymmetric (tau i) hLambdaI (yNet i)
    dsimp [u]
    rw [G.totalVaryingShiftResolventVector_of_lt
      T hInnerSymmetric tau lambdaNet yNet i hLambdaI]
    rw [hEquation]
    abel
  have hResidual :
      Tendsto
        (fun i =>
          T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
              hInnerSymmetric (tau i).1 (u i) - lambdaNet i • u i - yNet i)
        l (nhds 0) :=
    tendsto_const_nhds.congr' hResidualEventually.symm
  have hGraph :=
    G.approximateShiftedAdmissibleRescaledDefect_varyingShiftRhs_filter_graph_tendsto_continuumResolventGraphPoint
      T hP hInnerSymmetric hSelf l hlambda hTau hLambda hy hResidual
  simpa [VacuumSemigroupGapSlope.totalVaryingShiftResolventGraphPoint, u] using hGraph

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
