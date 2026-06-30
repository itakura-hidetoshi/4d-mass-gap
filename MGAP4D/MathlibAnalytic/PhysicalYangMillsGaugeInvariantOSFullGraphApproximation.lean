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

/-- Applying the continuum resolvent-selected domain construction to a shifted
closed-Hamiltonian graph point returns the original domain point. -/
@[simp] theorem VacuumSemigroupGapSlope.vacuumOrthogonalContinuumRealResolventDomainPoint_apply_realShift
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ}
    (hlambda : lambda < G.mass / 2)
    (x : (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf).domain) :
    G.vacuumOrthogonalContinuumRealResolventDomainPoint
        T hP hInnerSymmetric hSelf hlambda
        ((T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf).realShift
          lambda x) =
      x := by
  let A := T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
  let hASelf :=
    T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint_isSelfAdjoint
      hP hSelf
  let hGap :=
    G.vacuumOrthogonalClosedRightHamiltonian_halfGap
      T hP hInnerSymmetric hSelf
  change
    (A.realShiftLinearEquiv hASelf hlambda hGap).symm
        (A.realShift lambda x) = x
  rw [← LinearPMap.realShiftLinearEquiv_apply]
  exact (A.realShiftLinearEquiv hASelf hlambda hGap).symm_apply_apply x

/-- The continuous excitation resolvent is a left inverse of the shifted
closed Hamiltonian on its entire graph domain, not only on the canonical core. -/
@[simp] theorem VacuumSemigroupGapSlope.vacuumOrthogonalContinuumRealResolvent_apply_realShift
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ}
    (hlambda : lambda < G.mass / 2)
    (x : (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf).domain) :
    G.vacuumOrthogonalContinuumRealResolvent
        T hP hInnerSymmetric hSelf hlambda
        ((T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf).realShift
          lambda x) =
      (x : P.VacuumOrthogonalHilbert) := by
  rw [← G.vacuumOrthogonalContinuumRealResolventDomainPoint_coe
    T hP hInnerSymmetric hSelf hlambda]
  exact congrArg Subtype.val
    (G.vacuumOrthogonalContinuumRealResolventDomainPoint_apply_realShift
      T hP hInnerSymmetric hSelf hlambda x)

/-- Every continuum excitation-Hamiltonian graph-domain vector is the strong
limit of bounded rescaled-defect resolvent solutions driven by its shifted
closed-Hamiltonian value. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolvent_tendsto_continuumDomain
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ}
    (hlambda : lambda < G.mass / 2)
    (x : (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf).domain) :
    Tendsto
      (fun tau : G.AdmissibleRescaledDefectTime =>
        G.admissibleRescaledDefectResolvent
          hInnerSymmetric tau hlambda
          ((T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf).realShift
            lambda x))
      G.admissibleRescaledDefectTimeFilter
      (𝓝 (x : P.VacuumOrthogonalHilbert)) := by
  have h :=
    G.admissibleRescaledDefectResolvent_tendsto_continuumResolvent
      T hP hInnerSymmetric hSelf hlambda
      ((T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf).realShift
        lambda x)
  simpa only [G.vacuumOrthogonalContinuumRealResolvent_apply_realShift
    T hP hInnerSymmetric hSelf hlambda x] using h

/-- The corresponding bounded defect values converge to the closed continuum
Hamiltonian value at every graph-domain point. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefect_apply_resolvent_tendsto_closedRightHamiltonian
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ}
    (hlambda : lambda < G.mass / 2)
    (x : (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf).domain) :
    Tendsto
      (fun tau : G.AdmissibleRescaledDefectTime =>
        T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
          hInnerSymmetric tau.1
          (G.admissibleRescaledDefectResolvent
            hInnerSymmetric tau hlambda
            ((T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf).realShift
              lambda x)))
      G.admissibleRescaledDefectTimeFilter
      (𝓝
        (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf x)) := by
  have h :=
    G.admissibleRescaledDefect_apply_resolvent_tendsto_continuumHamiltonian
      T hP hInnerSymmetric hSelf hlambda
      ((T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf).realShift
        lambda x)
  simpa only [G.vacuumOrthogonalContinuumRealResolventDomainPoint_apply_realShift
    T hP hInnerSymmetric hSelf hlambda x] using h

/-- Every point of the graph of the closed continuum excitation Hamiltonian is
a product-topology limit of graph points of the bounded rescaled defects. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefect_graph_tendsto_continuumGraphPoint
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ}
    (hlambda : lambda < G.mass / 2)
    (x : (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf).domain) :
    Tendsto
      (fun tau : G.AdmissibleRescaledDefectTime =>
        let xTau :=
          G.admissibleRescaledDefectResolvent
            hInnerSymmetric tau hlambda
            ((T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf).realShift
              lambda x)
        (xTau,
          T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
            hInnerSymmetric tau.1 xTau))
      G.admissibleRescaledDefectTimeFilter
      (𝓝
        ((x : P.VacuumOrthogonalHilbert),
          T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf x)) := by
  rw [nhds_prod_eq]
  exact
    (G.admissibleRescaledDefectResolvent_tendsto_continuumDomain
      T hP hInnerSymmetric hSelf hlambda x).prodMk
      (G.admissibleRescaledDefect_apply_resolvent_tendsto_closedRightHamiltonian
        T hP hInnerSymmetric hSelf hlambda x)

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
