import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSFullStrongResolvent
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

/-- The graph-domain point selected by the continuum excitation resolvent. -/
noncomputable def VacuumSemigroupGapSlope.vacuumOrthogonalContinuumRealResolventDomainPoint
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ}
    (hlambda : lambda < G.mass / 2)
    (y : P.VacuumOrthogonalHilbert) :
    (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf).domain :=
  ((T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf).realShiftLinearEquiv
      (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint_isSelfAdjoint
        hP hSelf)
      hlambda
      (G.vacuumOrthogonalClosedRightHamiltonian_halfGap
        T hP hInnerSymmetric hSelf)).symm y

@[simp] theorem VacuumSemigroupGapSlope.vacuumOrthogonalContinuumRealResolventDomainPoint_coe
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ}
    (hlambda : lambda < G.mass / 2)
    (y : P.VacuumOrthogonalHilbert) :
    ((G.vacuumOrthogonalContinuumRealResolventDomainPoint
        T hP hInnerSymmetric hSelf hlambda y :
      (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf).domain) :
        P.VacuumOrthogonalHilbert) =
      G.vacuumOrthogonalContinuumRealResolvent
        T hP hInnerSymmetric hSelf hlambda y := by
  rfl

/-- Every bounded rescaled-defect resolvent solution satisfies its shifted
operator equation in the explicit unshifted form. -/
theorem VacuumSemigroupGapSlope.vacuumOrthogonalRescaledDefect_apply_admissibleResolvent_eq
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    {lambda : ℝ}
    (hlambda : lambda < G.mass / 2)
    (y : P.VacuumOrthogonalHilbert) :
    T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
        hInnerSymmetric tau.1
        (G.admissibleRescaledDefectResolvent
          hInnerSymmetric tau hlambda y) =
      y + lambda •
        G.admissibleRescaledDefectResolvent
          hInnerSymmetric tau hlambda y := by
  have hShift :=
    realHilbert_uniformCoerciveSymmetricStrongLimit_limitShift_apply_resolvent
      (G.admissibleRescaledDefectData hInnerSymmetric tau)
      hlambda y
  change
    T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
          hInnerSymmetric tau.1
          (G.admissibleRescaledDefectResolvent
            hInnerSymmetric tau hlambda y) -
        lambda •
          G.admissibleRescaledDefectResolvent
            hInnerSymmetric tau hlambda y = y at hShift
  exact (sub_eq_iff_eq_add).mp hShift

/-- The graph-closed continuum resolvent solution satisfies the corresponding
closed Hamiltonian equation. -/
theorem VacuumSemigroupGapSlope.vacuumOrthogonalClosedRightHamiltonian_apply_continuumResolventDomainPoint_eq
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ}
    (hlambda : lambda < G.mass / 2)
    (y : P.VacuumOrthogonalHilbert) :
    T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
        (G.vacuumOrthogonalContinuumRealResolventDomainPoint
          T hP hInnerSymmetric hSelf hlambda y) =
      y + lambda •
        G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf hlambda y := by
  let A := T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
  let hASelf :=
    T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint_isSelfAdjoint
      hP hSelf
  let hGap :=
    G.vacuumOrthogonalClosedRightHamiltonian_halfGap
      T hP hInnerSymmetric hSelf
  have hShift :=
    LinearPMap.realShift_realResolvent_preimage
      A hASelf hlambda hGap y
  change
    T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
          (G.vacuumOrthogonalContinuumRealResolventDomainPoint
            T hP hInnerSymmetric hSelf hlambda y) -
        lambda •
          G.vacuumOrthogonalContinuumRealResolvent
            T hP hInnerSymmetric hSelf hlambda y = y at hShift
  exact (sub_eq_iff_eq_add).mp hShift

/-- Along admissible small times, applying each bounded rescaled defect to its
resolvent solution converges strongly to the closed continuum Hamiltonian
applied to its resolvent-selected graph-domain point. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefect_apply_resolvent_tendsto_continuumHamiltonian
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ}
    (hlambda : lambda < G.mass / 2)
    (y : P.VacuumOrthogonalHilbert) :
    Tendsto
      (fun tau : G.AdmissibleRescaledDefectTime =>
        T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
          hInnerSymmetric tau.1
          (G.admissibleRescaledDefectResolvent
            hInnerSymmetric tau hlambda y))
      G.admissibleRescaledDefectTimeFilter
      (𝓝
        (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
          (G.vacuumOrthogonalContinuumRealResolventDomainPoint
            T hP hInnerSymmetric hSelf hlambda y))) := by
  have hResolvent :=
    G.admissibleRescaledDefectResolvent_tendsto_continuumResolvent
      T hP hInnerSymmetric hSelf hlambda y
  have hScaled :
      Tendsto
        (fun tau : G.AdmissibleRescaledDefectTime =>
          lambda •
            G.admissibleRescaledDefectResolvent
              hInnerSymmetric tau hlambda y)
        G.admissibleRescaledDefectTimeFilter
        (𝓝
          (lambda •
            G.vacuumOrthogonalContinuumRealResolvent
              T hP hInnerSymmetric hSelf hlambda y)) :=
    tendsto_const_nhds.smul hResolvent
  have hRight :
      Tendsto
        (fun tau : G.AdmissibleRescaledDefectTime =>
          y + lambda •
            G.admissibleRescaledDefectResolvent
              hInnerSymmetric tau hlambda y)
        G.admissibleRescaledDefectTimeFilter
        (𝓝
          (y + lambda •
            G.vacuumOrthogonalContinuumRealResolvent
              T hP hInnerSymmetric hSelf hlambda y)) :=
    tendsto_const_nhds.add hScaled
  have hApproximationFunction :
      (fun tau : G.AdmissibleRescaledDefectTime =>
        T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
          hInnerSymmetric tau.1
          (G.admissibleRescaledDefectResolvent
            hInnerSymmetric tau hlambda y)) =
      (fun tau : G.AdmissibleRescaledDefectTime =>
        y + lambda •
          G.admissibleRescaledDefectResolvent
            hInnerSymmetric tau hlambda y) := by
    funext tau
    exact
      G.vacuumOrthogonalRescaledDefect_apply_admissibleResolvent_eq
        T hInnerSymmetric tau hlambda y
  rw [hApproximationFunction]
  rw [G.vacuumOrthogonalClosedRightHamiltonian_apply_continuumResolventDomainPoint_eq
    T hP hInnerSymmetric hSelf hlambda y]
  exact hRight

/-- The resolvent-selected approximation converges in the product graph
topology: both the excitation vector and its Hamiltonian value converge. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefect_resolvent_graph_tendsto
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ}
    (hlambda : lambda < G.mass / 2)
    (y : P.VacuumOrthogonalHilbert) :
    Tendsto
      (fun tau : G.AdmissibleRescaledDefectTime =>
        (G.admissibleRescaledDefectResolvent
            hInnerSymmetric tau hlambda y,
          T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
            hInnerSymmetric tau.1
            (G.admissibleRescaledDefectResolvent
              hInnerSymmetric tau hlambda y)))
      G.admissibleRescaledDefectTimeFilter
      (𝓝
        (G.vacuumOrthogonalContinuumRealResolvent
            T hP hInnerSymmetric hSelf hlambda y,
          T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
            (G.vacuumOrthogonalContinuumRealResolventDomainPoint
              T hP hInnerSymmetric hSelf hlambda y))) := by
  rw [nhds_prod_eq]
  exact
    (G.admissibleRescaledDefectResolvent_tendsto_continuumResolvent
      T hP hInnerSymmetric hSelf hlambda y).prodMk
      (G.admissibleRescaledDefect_apply_resolvent_tendsto_continuumHamiltonian
        T hP hInnerSymmetric hSelf hlambda y)

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
