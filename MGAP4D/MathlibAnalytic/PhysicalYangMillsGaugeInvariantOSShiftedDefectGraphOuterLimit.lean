import MGAP4D.MathlibAnalytic.FilterKuratowskiOuterLimit
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

/-- Approximate shifted-defect graph points with residual norm bounded by
`epsilon i`. -/
def VacuumSemigroupGapSlope.approximateShiftedDefectGraphFamily
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {ι : Type*} (tau : ι → G.AdmissibleRescaledDefectTime)
    (lambdaNet : ι → ℝ) (yNet : ι → P.VacuumOrthogonalHilbert)
    (epsilon : ι → ℝ) (i : ι) :
    Set (P.VacuumOrthogonalHilbert × P.VacuumOrthogonalHilbert) :=
  {z |
    z.2 = T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
      hInnerSymmetric (tau i).1 z.1 ∧
    ‖T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
        hInnerSymmetric (tau i).1 z.1 - lambdaNet i • z.1 - yNet i‖ ≤ epsilon i}

@[simp]
theorem VacuumSemigroupGapSlope.mem_approximateShiftedDefectGraphFamily_iff
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {ι : Type*} (tau : ι → G.AdmissibleRescaledDefectTime)
    (lambdaNet : ι → ℝ) (yNet : ι → P.VacuumOrthogonalHilbert)
    (epsilon : ι → ℝ) (i : ι)
    (z : P.VacuumOrthogonalHilbert × P.VacuumOrthogonalHilbert) :
    z ∈ G.approximateShiftedDefectGraphFamily
      T hInnerSymmetric tau lambdaNet yNet epsilon i ↔
      z.2 = T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
        hInnerSymmetric (tau i).1 z.1 ∧
      ‖T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
          hInnerSymmetric (tau i).1 z.1 - lambdaNet i • z.1 - yNet i‖ ≤ epsilon i :=
  Iff.rfl

/-- The selection outer limit of approximate shifted-defect graph points is the
singleton canonical continuum resolvent graph point. -/
theorem VacuumSemigroupGapSlope.approximateShiftedDefectGraphFamily_selectionOuterLimit_subset_singleton
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) {ι : Type*} (l : Filter ι)
    {lambdaNet : ι → ℝ} {lambda : ℝ} (hlambda : lambda < G.mass / 2)
    {yNet : ι → P.VacuumOrthogonalHilbert} {y : P.VacuumOrthogonalHilbert}
    {tau : ι → G.AdmissibleRescaledDefectTime} {epsilon : ι → ℝ}
    (hTau : Tendsto tau l G.admissibleRescaledDefectTimeFilter)
    (hLambda : Tendsto lambdaNet l (nhds lambda)) (hy : Tendsto yNet l (nhds y))
    (hEpsilon : Tendsto epsilon l (nhds 0)) :
    Filter.selectionOuterLimit l
      (G.approximateShiftedDefectGraphFamily
        T hInnerSymmetric tau lambdaNet yNet epsilon) ⊆
      {(G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf hlambda y,
        T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
          (G.vacuumOrthogonalContinuumRealResolventDomainPoint
            T hP hInnerSymmetric hSelf hlambda y))} := by
  intro z hz
  rcases hz with ⟨v, hv, hCluster⟩
  let u : ι → P.VacuumOrthogonalHilbert := fun i => (v i).1
  have hGraphEq :
      v =ᶠ[l] fun i =>
        (u i, T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
          hInnerSymmetric (tau i).1 (u i)) := by
    filter_upwards [hv] with i hi
    exact Prod.ext rfl (by simpa [u] using hi.1)
  have hResidualNormLe :
      ∀ᶠ i in l,
        ‖T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
            hInnerSymmetric (tau i).1 (u i) - lambdaNet i • u i - yNet i‖ ≤
          epsilon i := by
    filter_upwards [hv] with i hi
    simpa [u] using hi.2
  have hResidual :
      Tendsto
        (fun i => T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
          hInnerSymmetric (tau i).1 (u i) - lambdaNet i • u i - yNet i)
        l (nhds 0) :=
    squeeze_zero_norm' hResidualNormLe hEpsilon
  let canonical : P.VacuumOrthogonalHilbert × P.VacuumOrthogonalHilbert :=
    (G.vacuumOrthogonalContinuumRealResolvent
        T hP hInnerSymmetric hSelf hlambda y,
      T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
        (G.vacuumOrthogonalContinuumRealResolventDomainPoint
          T hP hInnerSymmetric hSelf hlambda y))
  have hCanonical :
      Tendsto
        (fun i =>
          (u i, T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
            hInnerSymmetric (tau i).1 (u i)))
        l (nhds canonical) := by
    simpa [canonical] using
      G.approximateShiftedAdmissibleRescaledDefect_varyingShiftRhs_filter_graph_tendsto_continuumResolventGraphPoint
        T hP hInnerSymmetric hSelf l hlambda hTau hLambda hy hResidual
  have hvTendsto : Tendsto v l (nhds canonical) :=
    hCanonical.congr' hGraphEq.symm
  have hzCanonical : z = canonical := by
    apply eq_of_nhds_neBot
    exact hCluster.clusterPt.neBot.mono (inf_le_inf_left _ hvTendsto)
  simpa [canonical] using hzCanonical

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
