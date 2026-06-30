import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCoreShiftDenseRange
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumOrthogonalContinuousRealResolvent
import MGAP4D.MathlibAnalytic.UniformlyBoundedContinuousLinearMapDensePointwiseLimit
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

/-- The continuum excitation Hamiltonian retains the weaker half-mass Rayleigh
bound used uniformly by the bounded rescaled semigroup defects. -/
theorem VacuumSemigroupGapSlope.vacuumOrthogonalClosedRightHamiltonian_halfGap
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (x : (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf).domain) :
    (G.mass / 2) * ‖(x : P.VacuumOrthogonalHilbert)‖ ^ 2 ≤
      inner ℝ
        (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf x)
        (x : P.VacuumOrthogonalHilbert) := by
  have hFull :
      G.mass * ‖(x : P.VacuumOrthogonalHilbert)‖ ^ 2 ≤
        inner ℝ
          (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf x)
          (x : P.VacuumOrthogonalHilbert) := by
    simpa only [vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint] using
      G.vacuumOrthogonalClosedRightHamiltonian_gap
        T hP hInnerSymmetric x
  have hSq : 0 ≤ ‖(x : P.VacuumOrthogonalHilbert)‖ ^ 2 :=
    sq_nonneg _
  nlinarith [G.mass_pos]

/-- The graph-closed excitation Hamiltonian resolvent, normalized to the same
half-mass threshold used by the bounded defect resolvents. -/
noncomputable def VacuumSemigroupGapSlope.vacuumOrthogonalContinuumRealResolvent
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ}
    (hlambda : lambda < G.mass / 2) :
    P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert :=
  LinearPMap.realResolvent
    (A := T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf)
    (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint_isSelfAdjoint
      hP hSelf)
    hlambda
    (G.vacuumOrthogonalClosedRightHamiltonian_halfGap
      T hP hInnerSymmetric hSelf)

/-- The continuum resolvent inverts the closed Hamiltonian shift on every
canonical right-Hamiltonian core vector. -/
@[simp] theorem VacuumSemigroupGapSlope.vacuumOrthogonalContinuumRealResolvent_apply_coreShift
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ}
    (hlambda : lambda < G.mass / 2)
    (x : T.vacuumOrthogonalRightHamiltonianCoreDomain) :
    G.vacuumOrthogonalContinuumRealResolvent
        T hP hInnerSymmetric hSelf hlambda
        (T.vacuumOrthogonalClosedRightHamiltonianCoreShift
          hInnerSymmetric lambda x) =
      (x : P.VacuumOrthogonalHilbert) := by
  let A := T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
  let hASelf :=
    T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint_isSelfAdjoint
      hP hSelf
  let hGap :=
    G.vacuumOrthogonalClosedRightHamiltonian_halfGap
      T hP hInnerSymmetric hSelf
  let xDomain : A.domain :=
    T.vacuumOrthogonalRightHamiltonianCoreClosedDomainPoint x
  have hShift :
      T.vacuumOrthogonalClosedRightHamiltonianCoreShift
          hInnerSymmetric lambda x =
        A.realShift lambda xDomain := by
    rfl
  rw [hShift]
  change
    (((A.realShiftLinearEquiv hASelf hlambda hGap).symm
        (A.realShift lambda xDomain) : A.domain) :
      P.VacuumOrthogonalHilbert) =
        (x : P.VacuumOrthogonalHilbert)
  rw [← LinearPMap.realShiftLinearEquiv_apply]
  have hInverse :=
    (A.realShiftLinearEquiv hASelf hlambda hGap).symm_apply_apply xDomain
  exact congrArg Subtype.val hInverse

/-- The bounded rescaled-defect resolvents converge strongly to the resolvent of
the graph-closed excitation Hamiltonian on every excitation vector. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolvent_tendsto_continuumResolvent
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
        G.admissibleRescaledDefectResolvent
          hInnerSymmetric tau hlambda y)
      G.admissibleRescaledDefectTimeFilter
      (𝓝
        (G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf hlambda y)) := by
  let A : G.AdmissibleRescaledDefectTime →
      P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert :=
    fun tau =>
      G.admissibleRescaledDefectResolvent hInnerSymmetric tau hlambda
  let R : P.VacuumOrthogonalHilbert →L[ℝ]
      P.VacuumOrthogonalHilbert :=
    G.vacuumOrthogonalContinuumRealResolvent
      T hP hInnerSymmetric hSelf hlambda
  let K : NNReal :=
    ⟨(G.mass / 2 - lambda)⁻¹,
      inv_nonneg.mpr (sub_pos.mpr hlambda).le⟩
  let q : T.vacuumOrthogonalRightHamiltonianCoreDomain →
      P.VacuumOrthogonalHilbert :=
    fun x =>
      T.vacuumOrthogonalClosedRightHamiltonianCoreShift
        hInnerSymmetric lambda x
  have hA : ∀ tau, ‖A tau‖₊ ≤ K := by
    intro tau
    have hReal :
        ‖G.admissibleRescaledDefectResolvent
            hInnerSymmetric tau hlambda‖ ≤
          (G.mass / 2 - lambda)⁻¹ :=
      realHilbert_uniformCoerciveSymmetricStrongLimit_limitResolvent_norm_le
        (G.admissibleRescaledDefectData hInnerSymmetric tau)
        hlambda
    exact_mod_cast hReal
  have hq : DenseRange q := by
    simpa only [q] using
      G.vacuumOrthogonalClosedRightHamiltonianCoreShift_denseRange_halfMass
        T hP hInnerSymmetric hSelf hlambda
  have hRange : ∀ x : T.vacuumOrthogonalRightHamiltonianCoreDomain,
      Tendsto
        (fun tau => A tau (q x))
        G.admissibleRescaledDefectTimeFilter
        (𝓝 (R (q x))) := by
    intro x
    have hCore :=
      G.admissibleRescaledDefectResolvent_tendsto_on_coreShift
        T hInnerSymmetric hlambda x
    simpa only [A, R, q,
      G.vacuumOrthogonalContinuumRealResolvent_apply_coreShift
        T hP hInnerSymmetric hSelf hlambda x] using hCore
  exact
    uniformlyBoundedContinuousLinearMap_tendsto_of_denseRange
      A R K hA q hq hRange y

/-- Equivalent norm formulation of full strong-resolvent convergence. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolvent_sub_continuumResolvent_norm_tendsto_zero
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
        ‖G.admissibleRescaledDefectResolvent
              hInnerSymmetric tau hlambda y -
          G.vacuumOrthogonalContinuumRealResolvent
            T hP hInnerSymmetric hSelf hlambda y‖)
      G.admissibleRescaledDefectTimeFilter
      (𝓝 0) := by
  have h :=
    G.admissibleRescaledDefectResolvent_tendsto_continuumResolvent
      T hP hInnerSymmetric hSelf hlambda y
  have hSub := h.sub tendsto_const_nhds
  simpa using hSub.norm

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
