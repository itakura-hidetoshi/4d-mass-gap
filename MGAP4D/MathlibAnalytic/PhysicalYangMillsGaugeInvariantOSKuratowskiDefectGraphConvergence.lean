import MGAP4D.MathlibAnalytic.FilterKuratowskiInnerLimit
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSKuratowskiDefectGraphOuterLimit
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

/-- Eventual nonemptiness of the approximate shifted-defect graph family forces
the canonical continuum resolvent graph point into its Kuratowski inner limit. -/
theorem VacuumSemigroupGapSlope.canonicalPoint_mem_approximateShiftedDefectGraphFamily_kuratowskiInnerLimit
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) {ι : Type*} (l : Filter ι)
    [NeBot l] {lambdaNet : ι → ℝ} {lambda : ℝ} (hlambda : lambda < G.mass / 2)
    {yNet : ι → P.VacuumOrthogonalHilbert} {y : P.VacuumOrthogonalHilbert}
    {tau : ι → G.AdmissibleRescaledDefectTime} {epsilon : ι → ℝ}
    (hTau : Tendsto tau l G.admissibleRescaledDefectTimeFilter)
    (hLambda : Tendsto lambdaNet l (nhds lambda)) (hy : Tendsto yNet l (nhds y))
    (hEpsilon : Tendsto epsilon l (nhds 0))
    (hNonempty : ∀ᶠ i in l,
      (G.approximateShiftedDefectGraphFamily
        T hInnerSymmetric tau lambdaNet yNet epsilon i).Nonempty) :
    (G.vacuumOrthogonalContinuumRealResolvent
        T hP hInnerSymmetric hSelf hlambda y,
      T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
        (G.vacuumOrthogonalContinuumRealResolventDomainPoint
          T hP hInnerSymmetric hSelf hlambda y)) ∈
      FilterSet.kuratowskiInnerLimit l
        (G.approximateShiftedDefectGraphFamily
          T hInnerSymmetric tau lambdaNet yNet epsilon) := by
  classical
  let family := G.approximateShiftedDefectGraphFamily
    T hInnerSymmetric tau lambdaNet yNet epsilon
  let canonical : P.VacuumOrthogonalHilbert × P.VacuumOrthogonalHilbert :=
    (G.vacuumOrthogonalContinuumRealResolvent
        T hP hInnerSymmetric hSelf hlambda y,
      T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
        (G.vacuumOrthogonalContinuumRealResolventDomainPoint
          T hP hInnerSymmetric hSelf hlambda y))
  let selected : ι →
      P.VacuumOrthogonalHilbert × P.VacuumOrthogonalHilbert := fun i =>
    if hi : (family i).Nonempty then Classical.choose hi else canonical
  have hSelectedMem : ∀ᶠ i in l, selected i ∈ family i := by
    filter_upwards [hNonempty] with i hi
    dsimp [selected]
    rw [dif_pos hi]
    exact Classical.choose_spec hi
  let u : ι → P.VacuumOrthogonalHilbert := fun i => (selected i).1
  have hGraphEq :
      selected =ᶠ[l] fun i =>
        (u i, T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
          hInnerSymmetric (tau i).1 (u i)) := by
    filter_upwards [hSelectedMem] with i hi
    exact Prod.ext rfl (by simpa [family, u] using hi.1)
  have hResidualNormLe :
      ∀ᶠ i in l,
        ‖T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
            hInnerSymmetric (tau i).1 (u i) - lambdaNet i • u i - yNet i‖ ≤
          epsilon i := by
    filter_upwards [hSelectedMem] with i hi
    simpa [family, u] using hi.2
  have hResidual :
      Tendsto
        (fun i => T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
          hInnerSymmetric (tau i).1 (u i) - lambdaNet i • u i - yNet i)
        l (nhds 0) :=
    squeeze_zero_norm' hResidualNormLe hEpsilon
  have hCanonical :
      Tendsto
        (fun i =>
          (u i, T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
            hInnerSymmetric (tau i).1 (u i)))
        l (nhds canonical) := by
    simpa [canonical] using
      G.approximateShiftedAdmissibleRescaledDefect_varyingShiftRhs_filter_graph_tendsto_continuumResolventGraphPoint
        T hP hInnerSymmetric hSelf l hlambda hTau hLambda hy hResidual
  have hSelected : Tendsto selected l (nhds canonical) :=
    hCanonical.congr' hGraphEq.symm
  simpa [family, canonical] using
    FilterSet.mem_kuratowskiInnerLimit_of_tendsto_of_eventually_mem
      hSelected hSelectedMem

/-- Under eventual nonemptiness, both Painlevé–Kuratowski limits of the
approximate shifted-defect graph family equal the canonical singleton. -/
theorem VacuumSemigroupGapSlope.approximateShiftedDefectGraphFamily_kuratowskiLimits_eq_singleton
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) {ι : Type*} (l : Filter ι)
    [NeBot l] {lambdaNet : ι → ℝ} {lambda : ℝ} (hlambda : lambda < G.mass / 2)
    {yNet : ι → P.VacuumOrthogonalHilbert} {y : P.VacuumOrthogonalHilbert}
    {tau : ι → G.AdmissibleRescaledDefectTime} {epsilon : ι → ℝ}
    (hTau : Tendsto tau l G.admissibleRescaledDefectTimeFilter)
    (hLambda : Tendsto lambdaNet l (nhds lambda)) (hy : Tendsto yNet l (nhds y))
    (hEpsilon : Tendsto epsilon l (nhds 0))
    (hNonempty : ∀ᶠ i in l,
      (G.approximateShiftedDefectGraphFamily
        T hInnerSymmetric tau lambdaNet yNet epsilon i).Nonempty) :
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
  let family := G.approximateShiftedDefectGraphFamily
    T hInnerSymmetric tau lambdaNet yNet epsilon
  let canonical : P.VacuumOrthogonalHilbert × P.VacuumOrthogonalHilbert :=
    (G.vacuumOrthogonalContinuumRealResolvent
        T hP hInnerSymmetric hSelf hlambda y,
      T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
        (G.vacuumOrthogonalContinuumRealResolventDomainPoint
          T hP hInnerSymmetric hSelf hlambda y))
  have hCanonicalInner : canonical ∈ FilterSet.kuratowskiInnerLimit l family := by
    simpa [family, canonical] using
      G.canonicalPoint_mem_approximateShiftedDefectGraphFamily_kuratowskiInnerLimit
        T hP hInnerSymmetric hSelf l hlambda hTau hLambda hy hEpsilon hNonempty
  have hInnerOuter :
      FilterSet.kuratowskiInnerLimit l family ⊆
        FilterSet.kuratowskiOuterLimit l family :=
    FilterSet.kuratowskiInnerLimit_subset_kuratowskiOuterLimit l family
  have hOuterUpper :
      FilterSet.kuratowskiOuterLimit l family ⊆ {canonical} := by
    simpa [family, canonical] using
      G.approximateShiftedDefectGraphFamily_kuratowskiOuterLimit_subset_singleton
        T hP hInnerSymmetric hSelf l hlambda hTau hLambda hy hEpsilon
  have hSingletonInner : {canonical} ⊆ FilterSet.kuratowskiInnerLimit l family := by
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    exact hCanonicalInner
  have hInnerEq : FilterSet.kuratowskiInnerLimit l family = {canonical} :=
    Set.Subset.antisymm (hInnerOuter.trans hOuterUpper) hSingletonInner
  have hOuterEq : FilterSet.kuratowskiOuterLimit l family = {canonical} :=
    Set.Subset.antisymm hOuterUpper (hSingletonInner.trans hInnerOuter)
  simpa [family, canonical] using And.intro hInnerEq hOuterEq

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
