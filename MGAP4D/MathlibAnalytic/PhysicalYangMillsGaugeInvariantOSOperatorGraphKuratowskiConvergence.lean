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

/-- The ordinary graph of the bounded rescaled defect at each finite time. -/
def VacuumSemigroupGapSlope.rescaledDefectGraphFamily
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {ι : Type*} (tau : ι → G.AdmissibleRescaledDefectTime)
    (i : ι) :
    Set (P.VacuumOrthogonalHilbert × P.VacuumOrthogonalHilbert) :=
  {z | z.2 = T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
    hInnerSymmetric (tau i).1 z.1}

@[simp]
theorem VacuumSemigroupGapSlope.mem_rescaledDefectGraphFamily_iff
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {ι : Type*} (tau : ι → G.AdmissibleRescaledDefectTime)
    (i : ι) (z : P.VacuumOrthogonalHilbert × P.VacuumOrthogonalHilbert) :
    z ∈ G.rescaledDefectGraphFamily T hInnerSymmetric tau i ↔
      z.2 = T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
        hInnerSymmetric (tau i).1 z.1 :=
  Iff.rfl

/-- The ordinary graph of the closed continuum Hamiltonian on the
vacuum-orthogonal Hilbert space. -/
def VacuumSemigroupGapSlope.continuumHamiltonianGraph
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) :
    Set (P.VacuumOrthogonalHilbert × P.VacuumOrthogonalHilbert) :=
  {z | ∃ xDomain :
      (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf).domain,
    (xDomain : P.VacuumOrthogonalHilbert) = z.1 ∧
      T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf xDomain = z.2}

@[simp]
theorem VacuumSemigroupGapSlope.mem_continuumHamiltonianGraph_iff
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (z : P.VacuumOrthogonalHilbert × P.VacuumOrthogonalHilbert) :
    z ∈ G.continuumHamiltonianGraph T hSelf ↔
      ∃ xDomain :
        (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf).domain,
      (xDomain : P.VacuumOrthogonalHilbert) = z.1 ∧
        T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf xDomain = z.2 :=
  Iff.rfl

/-- Every filter outer-limit point of the ordinary finite-time graphs belongs
to the graph of the closed continuum Hamiltonian.  The shifted right-hand side
is reconstructed from the convergent graph coordinates. -/
theorem VacuumSemigroupGapSlope.rescaledDefectGraphFamily_kuratowskiOuterLimit_subset_continuumHamiltonianGraph
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
        (G.rescaledDefectGraphFamily T hInnerSymmetric tau) ⊆
      G.continuumHamiltonianGraph T hSelf := by
  intro z hz
  have hzConvergent :=
    FilterSet.kuratowskiOuterLimit_subset_convergentSelectionOuterLimit l
      (G.rescaledDefectGraphFamily T hInnerSymmetric tau) hz
  rcases hzConvergent with ⟨p, hp, hIndex, hPoint, hMem⟩
  letI : NeBot p := hp
  let u :
      (ι × (P.VacuumOrthogonalHilbert × P.VacuumOrthogonalHilbert)) →
        P.VacuumOrthogonalHilbert := fun w => w.2.1
  let tau' := fun w :
      ι × (P.VacuumOrthogonalHilbert × P.VacuumOrthogonalHilbert) => tau w.1
  let lambdaNet' := fun w :
      ι × (P.VacuumOrthogonalHilbert × P.VacuumOrthogonalHilbert) => lambdaNet w.1
  let source := fun w :
      ι × (P.VacuumOrthogonalHilbert × P.VacuumOrthogonalHilbert) =>
    T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
        hInnerSymmetric (tau' w).1 (u w) - lambdaNet' w • u w
  have hTau' : Tendsto tau' p G.admissibleRescaledDefectTimeFilter := by
    simpa [tau'] using hTau.comp hIndex
  have hLambda' : Tendsto lambdaNet' p (nhds lambda) := by
    simpa [lambdaNet'] using hLambda.comp hIndex
  have hU : Tendsto u p (nhds z.1) := by
    simpa [u] using (continuous_fst.tendsto z).comp hPoint
  have hValue :
      Tendsto (fun w => w.2.2) p (nhds z.2) := by
    simpa using (continuous_snd.tendsto z).comp hPoint
  have hValueEq :
      (fun w => w.2.2) =ᶠ[p] fun w =>
        T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
          hInnerSymmetric (tau' w).1 (u w) := by
    filter_upwards [hMem] with w hw
    simpa [u, tau'] using hw
  have hDefect :
      Tendsto
        (fun w => T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
          hInnerSymmetric (tau' w).1 (u w))
        p (nhds z.2) :=
    hValue.congr' hValueEq
  have hScaled :
      Tendsto (fun w => lambdaNet' w • u w) p
        (nhds (lambda • z.1)) :=
    hLambda'.smul hU
  have hSource : Tendsto source p (nhds (z.2 - lambda • z.1)) := by
    simpa [source] using hDefect.sub hScaled
  have hResidual :
      Tendsto
        (fun w =>
          T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
              hInnerSymmetric (tau' w).1 (u w) - lambdaNet' w • u w - source w)
        p (nhds 0) := by
    have hZero :
        (fun w =>
          T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
              hInnerSymmetric (tau' w).1 (u w) - lambdaNet' w • u w - source w) =
          fun _ => (0 : P.VacuumOrthogonalHilbert) := by
      funext w
      simp [source]
    rw [hZero]
    exact tendsto_const_nhds
  let canonical : P.VacuumOrthogonalHilbert × P.VacuumOrthogonalHilbert :=
    (G.vacuumOrthogonalContinuumRealResolvent
        T hP hInnerSymmetric hSelf hlambda (z.2 - lambda • z.1),
      T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
        (G.vacuumOrthogonalContinuumRealResolventDomainPoint
          T hP hInnerSymmetric hSelf hlambda (z.2 - lambda • z.1)))
  have hCanonical :
      Tendsto
        (fun w =>
          (u w, T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
            hInnerSymmetric (tau' w).1 (u w)))
        p (nhds canonical) := by
    simpa [canonical] using
      G.approximateShiftedAdmissibleRescaledDefect_varyingShiftRhs_filter_graph_tendsto_continuumResolventGraphPoint
        T hP hInnerSymmetric hSelf p hlambda hTau' hLambda' hSource hResidual
  have hSelectedEq :
      (fun w => w.2) =ᶠ[p] fun w =>
        (u w, T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
          hInnerSymmetric (tau' w).1 (u w)) := by
    filter_upwards [hMem] with w hw
    exact Prod.ext rfl (by simpa [u, tau'] using hw)
  have hSelectedCanonical : Tendsto (fun w => w.2) p (nhds canonical) :=
    hCanonical.congr' hSelectedEq.symm
  have hzEq : z = canonical :=
    tendsto_nhds_unique hPoint hSelectedCanonical
  rw [hzEq]
  refine ⟨G.vacuumOrthogonalContinuumRealResolventDomainPoint
      T hP hInnerSymmetric hSelf hlambda (z.2 - lambda • z.1), ?_, rfl⟩
  exact G.vacuumOrthogonalContinuumRealResolventDomainPoint_coe
    T hP hInnerSymmetric hSelf hlambda (z.2 - lambda • z.1)

/-- Every continuum Hamiltonian graph point has a finite-time resolvent recovery
net in the ordinary defect graphs. -/
theorem VacuumSemigroupGapSlope.continuumHamiltonianGraph_subset_rescaledDefectGraphFamily_kuratowskiInnerLimit
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
    G.continuumHamiltonianGraph T hSelf ⊆
      FilterSet.kuratowskiInnerLimit l
        (G.rescaledDefectGraphFamily T hInnerSymmetric tau) := by
  intro z hz
  rcases hz with ⟨xDomain, hxFirst, hxSecond⟩
  let A := T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
  let hASelf :=
    T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint_isSelfAdjoint
      hP hSelf
  let hGap :=
    G.vacuumOrthogonalClosedRightHamiltonian_halfGap
      T hP hInnerSymmetric hSelf
  let y : P.VacuumOrthogonalHilbert := A.realShift lambda xDomain
  let yNet : ι → P.VacuumOrthogonalHilbert := fun _ => y
  let recovery : ι →
      P.VacuumOrthogonalHilbert × P.VacuumOrthogonalHilbert :=
    G.totalVaryingShiftResolventGraphPoint
      T hInnerSymmetric tau lambdaNet yNet
  have hDomain :
      G.vacuumOrthogonalContinuumRealResolventDomainPoint
          T hP hInnerSymmetric hSelf hlambda y = xDomain := by
    change
      (A.realShiftLinearEquiv hASelf hlambda hGap).symm
          (A.realShift lambda xDomain) = xDomain
    rw [← LinearPMap.realShiftLinearEquiv_apply]
    exact (A.realShiftLinearEquiv hASelf hlambda hGap).symm_apply_apply xDomain
  have hCanonicalEq :
      (G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf hlambda y,
        T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
          (G.vacuumOrthogonalContinuumRealResolventDomainPoint
            T hP hInnerSymmetric hSelf hlambda y)) = z := by
    apply Prod.ext
    · calc
        G.vacuumOrthogonalContinuumRealResolvent
            T hP hInnerSymmetric hSelf hlambda y =
            ((G.vacuumOrthogonalContinuumRealResolventDomainPoint
              T hP hInnerSymmetric hSelf hlambda y) :
                P.VacuumOrthogonalHilbert) := by
              symm
              exact G.vacuumOrthogonalContinuumRealResolventDomainPoint_coe
                T hP hInnerSymmetric hSelf hlambda y
        _ = (xDomain : P.VacuumOrthogonalHilbert) :=
          congrArg Subtype.val hDomain
        _ = z.1 := hxFirst
    · calc
        T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
            (G.vacuumOrthogonalContinuumRealResolventDomainPoint
              T hP hInnerSymmetric hSelf hlambda y) =
            T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf xDomain := by
              rw [hDomain]
        _ = z.2 := hxSecond
  have hRecovery : Tendsto recovery l (nhds z) := by
    have h :=
      G.totalVaryingShiftResolventGraphPoint_tendsto_continuum
        T hP hInnerSymmetric hSelf l hlambda hTau hLambda
          (tendsto_const_nhds : Tendsto (fun _ : ι => y) l (nhds y))
    simpa [recovery, yNet, hCanonicalEq] using h
  have hRecoveryMem :
      ∀ᶠ i in l,
        recovery i ∈ G.rescaledDefectGraphFamily T hInnerSymmetric tau i := by
    exact Eventually.of_forall fun i => by
      simp [recovery, VacuumSemigroupGapSlope.totalVaryingShiftResolventGraphPoint,
        VacuumSemigroupGapSlope.rescaledDefectGraphFamily]
  exact FilterSet.mem_kuratowskiInnerLimit_of_tendsto_of_eventually_mem
    hRecovery hRecoveryMem

/-- The ordinary graphs of the bounded rescaled defects converge, along every
nontrivial small-time filter, to the graph of the closed continuum Hamiltonian
in the full Painlevé–Kuratowski sense. -/
theorem VacuumSemigroupGapSlope.rescaledDefectGraphFamily_kuratowskiLimits_eq_continuumHamiltonianGraph
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
        (G.rescaledDefectGraphFamily T hInnerSymmetric tau) =
      G.continuumHamiltonianGraph T hSelf ∧
    FilterSet.kuratowskiOuterLimit l
        (G.rescaledDefectGraphFamily T hInnerSymmetric tau) =
      G.continuumHamiltonianGraph T hSelf := by
  let family := G.rescaledDefectGraphFamily T hInnerSymmetric tau
  let continuum := G.continuumHamiltonianGraph T hSelf
  have hOuter : FilterSet.kuratowskiOuterLimit l family ⊆ continuum := by
    simpa [family, continuum] using
      G.rescaledDefectGraphFamily_kuratowskiOuterLimit_subset_continuumHamiltonianGraph
        T hP hInnerSymmetric hSelf l hlambda hTau hLambda
  have hRecovery : continuum ⊆ FilterSet.kuratowskiInnerLimit l family := by
    simpa [family, continuum] using
      G.continuumHamiltonianGraph_subset_rescaledDefectGraphFamily_kuratowskiInnerLimit
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
