import MGAP4D.MathlibAnalytic.FilterKuratowskiInnerLimit
import MGAP4D.MathlibAnalytic.FilterKuratowskiOuterLimitSubnet
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSTotalVaryingResolventGraphPoint
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

/-- The full exact shifted graph at one finite rescaled-defect time.  The source
is retained as the first coordinate instead of being fixed in advance. -/
def VacuumSemigroupGapSlope.fullExactShiftedDefectGraphFamily
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {ι : Type*} (tau : ι → G.AdmissibleRescaledDefectTime)
    (lambdaNet : ι → ℝ) (i : ι) :
    Set (P.VacuumOrthogonalHilbert ×
      (P.VacuumOrthogonalHilbert × P.VacuumOrthogonalHilbert)) :=
  {z |
    z.2.2 = T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
      hInnerSymmetric (tau i).1 z.2.1 ∧
    T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
        hInnerSymmetric (tau i).1 z.2.1 - lambdaNet i • z.2.1 = z.1}

@[simp]
theorem VacuumSemigroupGapSlope.mem_fullExactShiftedDefectGraphFamily_iff
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {ι : Type*} (tau : ι → G.AdmissibleRescaledDefectTime)
    (lambdaNet : ι → ℝ) (i : ι)
    (z : P.VacuumOrthogonalHilbert ×
      (P.VacuumOrthogonalHilbert × P.VacuumOrthogonalHilbert)) :
    z ∈ G.fullExactShiftedDefectGraphFamily
      T hInnerSymmetric tau lambdaNet i ↔
      z.2.2 = T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
        hInnerSymmetric (tau i).1 z.2.1 ∧
      T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
          hInnerSymmetric (tau i).1 z.2.1 - lambdaNet i • z.2.1 = z.1 :=
  Iff.rfl

/-- The continuum shifted Hamiltonian graph, parametrized by its source through
the continuum resolvent. -/
def VacuumSemigroupGapSlope.continuumShiftedResolventGraph
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ} (hlambda : lambda < G.mass / 2) :
    Set (P.VacuumOrthogonalHilbert ×
      (P.VacuumOrthogonalHilbert × P.VacuumOrthogonalHilbert)) :=
  Set.range fun y =>
    (y,
      (G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf hlambda y,
        T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
          (G.vacuumOrthogonalContinuumRealResolventDomainPoint
            T hP hInnerSymmetric hSelf hlambda y)))

/-- Every full finite-time outer-limit point is a continuum shifted-resolvent
graph point.  Convergence of the source coordinate supplies the varying right
hand side required by the arbitrary-filter graph convergence theorem. -/
theorem VacuumSemigroupGapSlope.fullExactShiftedDefectGraphFamily_kuratowskiOuterLimit_subset_continuumShiftedResolventGraph
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {ι : Type*} (l : Filter ι)
    {tau : ι → G.AdmissibleRescaledDefectTime}
    {lambdaNet : ι → ℝ} {lambda : ℝ}
    (hlambda : lambda < G.mass / 2)
    (hTau : Tendsto tau l G.admissibleRescaledDefectTimeFilter)
    (hLambda : Tendsto lambdaNet l (nhds lambda)) :
    FilterSet.kuratowskiOuterLimit l
        (G.fullExactShiftedDefectGraphFamily
          T hInnerSymmetric tau lambdaNet) ⊆
      G.continuumShiftedResolventGraph
        T hP hInnerSymmetric hSelf hlambda := by
  intro z hz
  have hzConvergent :=
    FilterSet.kuratowskiOuterLimit_subset_convergentSelectionOuterLimit l
      (G.fullExactShiftedDefectGraphFamily
        T hInnerSymmetric tau lambdaNet) hz
  rcases hzConvergent with ⟨p, hp, hIndex, hPoint, hMem⟩
  letI : NeBot p := hp
  let source :
      (ι × (P.VacuumOrthogonalHilbert ×
        (P.VacuumOrthogonalHilbert × P.VacuumOrthogonalHilbert))) →
        P.VacuumOrthogonalHilbert := fun w => w.2.1
  let u :
      (ι × (P.VacuumOrthogonalHilbert ×
        (P.VacuumOrthogonalHilbert × P.VacuumOrthogonalHilbert))) →
        P.VacuumOrthogonalHilbert := fun w => w.2.2.1
  let tau' := fun w :
      ι × (P.VacuumOrthogonalHilbert ×
        (P.VacuumOrthogonalHilbert × P.VacuumOrthogonalHilbert)) => tau w.1
  let lambdaNet' := fun w :
      ι × (P.VacuumOrthogonalHilbert ×
        (P.VacuumOrthogonalHilbert × P.VacuumOrthogonalHilbert)) => lambdaNet w.1
  have hTau' : Tendsto tau' p G.admissibleRescaledDefectTimeFilter := by
    simpa [tau'] using hTau.comp hIndex
  have hLambda' : Tendsto lambdaNet' p (nhds lambda) := by
    simpa [lambdaNet'] using hLambda.comp hIndex
  have hSource : Tendsto source p (nhds z.1) := by
    simpa [source] using (continuous_fst.tendsto z).comp hPoint
  have hSelectedGraph : Tendsto (fun w => w.2.2) p (nhds z.2) := by
    simpa using (continuous_snd.tendsto z).comp hPoint
  have hGraphEq :
      (fun w => w.2.2) =ᶠ[p] fun w =>
        (u w, T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
          hInnerSymmetric (tau' w).1 (u w)) := by
    filter_upwards [hMem] with w hw
    exact Prod.ext rfl (by simpa [u, tau'] using hw.1)
  have hResidualEventually :
      ∀ᶠ w in p,
        T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
            hInnerSymmetric (tau' w).1 (u w) - lambdaNet' w • u w - source w = 0 := by
    filter_upwards [hMem] with w hw
    have hEquation :
        T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
            hInnerSymmetric (tau' w).1 (u w) - lambdaNet' w • u w = source w := by
      simpa [u, tau', lambdaNet', source] using hw.2
    rw [hEquation]
    abel
  have hResidualEq :
      (fun _ => (0 : P.VacuumOrthogonalHilbert)) =ᶠ[p]
        (fun w =>
          T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
              hInnerSymmetric (tau' w).1 (u w) - lambdaNet' w • u w - source w) := by
    filter_upwards [hResidualEventually] with w hw
    exact hw.symm
  have hResidual :
      Tendsto
        (fun w =>
          T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
              hInnerSymmetric (tau' w).1 (u w) - lambdaNet' w • u w - source w)
        p (nhds 0) :=
    tendsto_const_nhds.congr' hResidualEq
  let canonicalGraph :
      P.VacuumOrthogonalHilbert × P.VacuumOrthogonalHilbert :=
    (G.vacuumOrthogonalContinuumRealResolvent
        T hP hInnerSymmetric hSelf hlambda z.1,
      T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
        (G.vacuumOrthogonalContinuumRealResolventDomainPoint
          T hP hInnerSymmetric hSelf hlambda z.1))
  have hCanonicalGraph :
      Tendsto
        (fun w =>
          (u w, T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
            hInnerSymmetric (tau' w).1 (u w)))
        p (nhds canonicalGraph) := by
    simpa [canonicalGraph] using
      G.approximateShiftedAdmissibleRescaledDefect_varyingShiftRhs_filter_graph_tendsto_continuumResolventGraphPoint
        T hP hInnerSymmetric hSelf p hlambda hTau' hLambda' hSource hResidual
  have hSelectedCanonical : Tendsto (fun w => w.2.2) p (nhds canonicalGraph) :=
    hCanonicalGraph.congr' hGraphEq.symm
  have hzGraph : z.2 = canonicalGraph :=
    tendsto_nhds_unique hSelectedGraph hSelectedCanonical
  refine ⟨z.1, ?_⟩
  apply Prod.ext
  · rfl
  · exact hzGraph.symm

/-- Every continuum shifted-resolvent graph point has a finite-time exact
recovery net and therefore belongs to the Kuratowski inner limit. -/
theorem VacuumSemigroupGapSlope.continuumShiftedResolventGraph_subset_fullExactShiftedDefectGraphFamily_kuratowskiInnerLimit
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {ι : Type*} (l : Filter ι)
    {tau : ι → G.AdmissibleRescaledDefectTime}
    {lambdaNet : ι → ℝ} {lambda : ℝ}
    (hlambda : lambda < G.mass / 2)
    (hTau : Tendsto tau l G.admissibleRescaledDefectTimeFilter)
    (hLambda : Tendsto lambdaNet l (nhds lambda)) :
    G.continuumShiftedResolventGraph
        T hP hInnerSymmetric hSelf hlambda ⊆
      FilterSet.kuratowskiInnerLimit l
        (G.fullExactShiftedDefectGraphFamily
          T hInnerSymmetric tau lambdaNet) := by
  intro z hz
  rcases hz with ⟨y, rfl⟩
  let yNet : ι → P.VacuumOrthogonalHilbert := fun _ => y
  let recovery : ι →
      P.VacuumOrthogonalHilbert ×
        (P.VacuumOrthogonalHilbert × P.VacuumOrthogonalHilbert) := fun i =>
    (y, G.totalVaryingShiftResolventGraphPoint
      T hInnerSymmetric tau lambdaNet yNet i)
  have hGraphTendsto :
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
    simpa [yNet] using
      G.totalVaryingShiftResolventGraphPoint_tendsto_continuum
        T hP hInnerSymmetric hSelf l hlambda hTau hLambda
          (tendsto_const_nhds : Tendsto (fun _ : ι => y) l (nhds y))
  have hRecovery :
      Tendsto recovery l
        (nhds
          (y,
            (G.vacuumOrthogonalContinuumRealResolvent
                T hP hInnerSymmetric hSelf hlambda y,
              T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
                (G.vacuumOrthogonalContinuumRealResolventDomainPoint
                  T hP hInnerSymmetric hSelf hlambda y)))) := by
    simpa [recovery] using tendsto_const_nhds.prodMk hGraphTendsto
  have hSingleton :
      ∀ᶠ i in l,
        G.exactShiftedDefectGraphFamily
            T hInnerSymmetric tau lambdaNet yNet i =
          {G.totalVaryingShiftResolventGraphPoint
            T hInnerSymmetric tau lambdaNet yNet i} :=
    G.exactShiftedDefectGraphFamily_eventually_eq_singleton_totalGraphPoint
      T hInnerSymmetric l hLambda hlambda
  have hRecoveryMem :
      ∀ᶠ i in l,
        recovery i ∈ G.fullExactShiftedDefectGraphFamily
          T hInnerSymmetric tau lambdaNet i := by
    filter_upwards [hSingleton] with i hi
    have hFixedMem :
        G.totalVaryingShiftResolventGraphPoint
            T hInnerSymmetric tau lambdaNet yNet i ∈
          G.exactShiftedDefectGraphFamily
            T hInnerSymmetric tau lambdaNet yNet i := by
      rw [hi]
      simp
    simpa [recovery, yNet,
      VacuumSemigroupGapSlope.fullExactShiftedDefectGraphFamily] using hFixedMem
  exact FilterSet.mem_kuratowskiInnerLimit_of_tendsto_of_eventually_mem
    hRecovery hRecoveryMem

/-- The full exact shifted finite-time graphs converge in the
Painlevé–Kuratowski sense to the entire continuum shifted-resolvent graph. -/
theorem VacuumSemigroupGapSlope.fullExactShiftedDefectGraphFamily_kuratowskiLimits_eq_continuumShiftedResolventGraph
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {ι : Type*} (l : Filter ι) [NeBot l]
    {tau : ι → G.AdmissibleRescaledDefectTime}
    {lambdaNet : ι → ℝ} {lambda : ℝ}
    (hlambda : lambda < G.mass / 2)
    (hTau : Tendsto tau l G.admissibleRescaledDefectTimeFilter)
    (hLambda : Tendsto lambdaNet l (nhds lambda)) :
    FilterSet.kuratowskiInnerLimit l
        (G.fullExactShiftedDefectGraphFamily
          T hInnerSymmetric tau lambdaNet) =
      G.continuumShiftedResolventGraph
        T hP hInnerSymmetric hSelf hlambda ∧
    FilterSet.kuratowskiOuterLimit l
        (G.fullExactShiftedDefectGraphFamily
          T hInnerSymmetric tau lambdaNet) =
      G.continuumShiftedResolventGraph
        T hP hInnerSymmetric hSelf hlambda := by
  let family := G.fullExactShiftedDefectGraphFamily
    T hInnerSymmetric tau lambdaNet
  let continuum := G.continuumShiftedResolventGraph
    T hP hInnerSymmetric hSelf hlambda
  have hOuter : FilterSet.kuratowskiOuterLimit l family ⊆ continuum := by
    simpa [family, continuum] using
      G.fullExactShiftedDefectGraphFamily_kuratowskiOuterLimit_subset_continuumShiftedResolventGraph
        T hP hInnerSymmetric hSelf l hlambda hTau hLambda
  have hRecovery : continuum ⊆ FilterSet.kuratowskiInnerLimit l family := by
    simpa [family, continuum] using
      G.continuumShiftedResolventGraph_subset_fullExactShiftedDefectGraphFamily_kuratowskiInnerLimit
        T hP hInnerSymmetric hSelf l hlambda hTau hLambda
  have hInnerOuter :
      FilterSet.kuratowskiInnerLimit l family ⊆
        FilterSet.kuratowskiOuterLimit l family :=
    FilterSet.kuratowskiInnerLimit_subset_kuratowskiOuterLimit l family
  have hInnerEq : FilterSet.kuratowskiInnerLimit l family = continuum :=
    Set.Subset.antisymm (hInnerOuter.trans hOuter) hRecovery
  have hOuterEq : FilterSet.kuratowskiOuterLimit l family = continuum :=
    Set.Subset.antisymm hOuter (hRecovery.trans hInnerOuter)
  simpa [family, continuum] using And.intro hInnerEq hOuterEq

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
