import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorStrongLimit
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalOperatorLimitPackage
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalResolventPowers
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalResolventIdentity
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumOrthogonalRealResolventIdentity
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped InnerProductSpace LinearPMap ContDiff

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 3200000

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- The proof-indexed finite-time resolvent, totalized outside the common
half-mass domain. -/
noncomputable def VacuumSemigroupGapSlope.admissibleRescaledDefectTaylorResolvent
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime) :
    ℝ → P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert :=
  belowGapContinuousLinearMapFamily (G.mass / 2)
    (fun lambda hlambda =>
      G.admissibleRescaledDefectResolvent
        hInnerSymmetric tau hlambda)

@[simp]
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectTaylorResolvent_of_lt
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    {lambda : ℝ} (hlambda : lambda < G.mass / 2) :
    G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric tau lambda =
      G.admissibleRescaledDefectResolvent
        hInnerSymmetric tau hlambda := by
  simp [VacuumSemigroupGapSlope.admissibleRescaledDefectTaylorResolvent,
    hlambda]

/-- The proof-indexed continuum excitation resolvent, totalized outside the
same common half-mass domain. -/
noncomputable def VacuumSemigroupGapSlope.vacuumOrthogonalContinuumTaylorResolvent
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) :
    ℝ → P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert :=
  belowGapContinuousLinearMapFamily (G.mass / 2)
    (fun lambda hlambda =>
      G.vacuumOrthogonalContinuumRealResolvent
        T hP hInnerSymmetric hSelf hlambda)

@[simp]
theorem VacuumSemigroupGapSlope.vacuumOrthogonalContinuumTaylorResolvent_of_lt
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ} (hlambda : lambda < G.mass / 2) :
    G.vacuumOrthogonalContinuumTaylorResolvent
        T hP hInnerSymmetric hSelf lambda =
      G.vacuumOrthogonalContinuumRealResolvent
        T hP hInnerSymmetric hSelf hlambda := by
  simp [VacuumSemigroupGapSlope.vacuumOrthogonalContinuumTaylorResolvent,
    hlambda]

/-- The common coercive bound and finite-time resolvent identity yield the
standard two-parameter operator-norm modulus. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolvent_sub_norm_le
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    {lambda mu : ℝ}
    (hlambda : lambda < G.mass / 2)
    (hmu : mu < G.mass / 2) :
    ‖G.admissibleRescaledDefectResolvent hInnerSymmetric tau hlambda -
        G.admissibleRescaledDefectResolvent hInnerSymmetric tau hmu‖ ≤
      |lambda - mu| *
        (((G.mass / 2) - lambda)⁻¹ * ((G.mass / 2) - mu)⁻¹) := by
  let Rlambda :=
    G.admissibleRescaledDefectResolvent hInnerSymmetric tau hlambda
  let Rmu :=
    G.admissibleRescaledDefectResolvent hInnerSymmetric tau hmu
  have hLambdaNorm : ‖Rlambda‖ ≤ ((G.mass / 2) - lambda)⁻¹ := by
    simpa [Rlambda] using
      realHilbert_uniformCoerciveSymmetricStrongLimit_limitResolvent_norm_le
        (G.admissibleRescaledDefectData hInnerSymmetric tau) hlambda
  have hMuNorm : ‖Rmu‖ ≤ ((G.mass / 2) - mu)⁻¹ := by
    simpa [Rmu] using
      realHilbert_uniformCoerciveSymmetricStrongLimit_limitResolvent_norm_le
        (G.admissibleRescaledDefectData hInnerSymmetric tau) hmu
  rw [G.admissibleRescaledDefectResolvent_identity
    T hInnerSymmetric tau hlambda hmu]
  apply ContinuousLinearMap.opNorm_le_bound
  · positivity
  · intro y
    change ‖(lambda - mu) • Rlambda (Rmu y)‖ ≤
      (|lambda - mu| *
        (((G.mass / 2) - lambda)⁻¹ * ((G.mass / 2) - mu)⁻¹)) * ‖y‖
    rw [norm_smul, Real.norm_eq_abs]
    have hLambdaApply :
        ‖Rlambda (Rmu y)‖ ≤
          ((G.mass / 2) - lambda)⁻¹ * ‖Rmu y‖ :=
      Rlambda.le_of_opNorm_le hLambdaNorm (Rmu y)
    have hMuApply :
        ‖Rmu y‖ ≤ ((G.mass / 2) - mu)⁻¹ * ‖y‖ :=
      Rmu.le_of_opNorm_le hMuNorm y
    calc
      |lambda - mu| * ‖Rlambda (Rmu y)‖ ≤
          |lambda - mu| *
            (((G.mass / 2) - lambda)⁻¹ * ‖Rmu y‖) :=
        mul_le_mul_of_nonneg_left hLambdaApply (abs_nonneg _)
      _ ≤ |lambda - mu| *
          (((G.mass / 2) - lambda)⁻¹ *
            (((G.mass / 2) - mu)⁻¹ * ‖y‖)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hMuApply
            (inv_nonneg.mpr (sub_nonneg.mpr hlambda.le)))
          (abs_nonneg _)
      _ = (|lambda - mu| *
          (((G.mass / 2) - lambda)⁻¹ * ((G.mass / 2) - mu)⁻¹)) * ‖y‖ := by
        ring

/-- The continuum excitation resolvent has the same two-parameter reciprocal
half-gap modulus. -/
theorem VacuumSemigroupGapSlope.vacuumOrthogonalContinuumRealResolvent_sub_norm_le
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda mu : ℝ}
    (hlambda : lambda < G.mass / 2)
    (hmu : mu < G.mass / 2) :
    ‖G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf hlambda -
        G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf hmu‖ ≤
      |lambda - mu| *
        (((G.mass / 2) - lambda)⁻¹ * ((G.mass / 2) - mu)⁻¹) := by
  exact LinearPMap.realResolvent_sub_norm_le
    (A := T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf)
    (hSelf :=
      T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint_isSelfAdjoint
        hP hSelf)
    hlambda hmu
    (G.vacuumOrthogonalClosedRightHamiltonian_halfGap
      T hP hInnerSymmetric hSelf)

/-- Abstract open-resolvent calculus for every admissible finite time. -/
noncomputable def VacuumSemigroupGapSlope.admissibleRescaledDefectOpenResolventData
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime) :
    ContinuousLinearMapOpenResolventData P.VacuumOrthogonalHilbert :=
  ContinuousLinearMapOpenResolventData.ofBelowGapFamily
    (G.mass / 2)
    (fun lambda hlambda =>
      G.admissibleRescaledDefectResolvent hInnerSymmetric tau hlambda)
    (G.admissibleRescaledDefectResolvent_sub_norm_le
      T hInnerSymmetric tau)
    (G.admissibleRescaledDefectResolvent_identity
      T hInnerSymmetric tau)

/-- Abstract open-resolvent calculus for the continuum excitation Hamiltonian. -/
noncomputable def VacuumSemigroupGapSlope.vacuumOrthogonalContinuumOpenResolventData
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) :
    ContinuousLinearMapOpenResolventData P.VacuumOrthogonalHilbert :=
  ContinuousLinearMapOpenResolventData.ofBelowGapFamily
    (G.mass / 2)
    (fun lambda hlambda =>
      G.vacuumOrthogonalContinuumRealResolvent
        T hP hInnerSymmetric hSelf hlambda)
    (G.vacuumOrthogonalContinuumRealResolvent_sub_norm_le
      T hP hInnerSymmetric hSelf)
    (G.vacuumOrthogonalContinuumRealResolvent_identity
      T hP hInnerSymmetric hSelf)

/-- Every finite-time totalized resolvent is smooth on the common sub-gap
interval and has the exact factorial derivative formula. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectTaylorResolvent_iteratedDeriv
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    (k : ℕ) {lambda : ℝ} (hlambda : lambda < G.mass / 2) :
    iteratedDeriv k
        (G.admissibleRescaledDefectTaylorResolvent
          T hInnerSymmetric tau) lambda =
      (k.factorial : ℝ) •
        (G.admissibleRescaledDefectTaylorResolvent
          T hInnerSymmetric tau lambda) ^ (k + 1) := by
  exact
    (G.admissibleRescaledDefectOpenResolventData
      T hInnerSymmetric tau).iteratedDeriv k hlambda

/-- The continuum totalized resolvent has the same exact factorial derivative
formula on the common sub-gap interval. -/
theorem VacuumSemigroupGapSlope.vacuumOrthogonalContinuumTaylorResolvent_iteratedDeriv
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (k : ℕ) {lambda : ℝ} (hlambda : lambda < G.mass / 2) :
    iteratedDeriv k
        (G.vacuumOrthogonalContinuumTaylorResolvent
          T hP hInnerSymmetric hSelf) lambda =
      (k.factorial : ℝ) •
        (G.vacuumOrthogonalContinuumTaylorResolvent
          T hP hInnerSymmetric hSelf lambda) ^ (k + 1) := by
  exact
    (G.vacuumOrthogonalContinuumOpenResolventData
      T hP hInnerSymmetric hSelf).iteratedDeriv k hlambda

/-- The actual uniform-coercive strong resolvent limit canonically generates
all-order Taylor strong-limit data on the physical vacuum-orthogonal sector. -/
noncomputable def VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorStrongLimitData
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) :
    ContinuousLinearMapOpenTaylorStrongLimitData
      G.admissibleRescaledDefectTimeFilter (G.mass / 2)
      (fun tau =>
        G.admissibleRescaledDefectTaylorResolvent
          T hInnerSymmetric tau) :=
  ContinuousLinearMapOpenTaylorStrongLimitData.of_resolventPowers
    (R := G.vacuumOrthogonalContinuumTaylorResolvent
      T hP hInnerSymmetric hSelf)
    (fun hmu x => by
      simpa only [
        G.admissibleRescaledDefectTaylorResolvent_of_lt
          T hInnerSymmetric _ hmu,
        G.vacuumOrthogonalContinuumTaylorResolvent_of_lt
          T hP hInnerSymmetric hSelf hmu] using
        G.admissibleRescaledDefectResolvent_tendsto_continuumResolvent
          T hP hInnerSymmetric hSelf hmu x)
    (fun k hlambda x => by
      simpa only [
        G.admissibleRescaledDefectTaylorResolvent_of_lt
          T hInnerSymmetric _ hlambda,
        G.vacuumOrthogonalContinuumTaylorResolvent_of_lt
          T hP hInnerSymmetric hSelf hlambda] using
        G.admissibleRescaledDefectResolvent_pow_tendsto_continuumResolvent_pow
          T hP hInnerSymmetric hSelf hlambda (k + 1) x)
    (fun tau k lambda hlambda =>
      G.admissibleRescaledDefectTaylorResolvent_iteratedDeriv
        T hInnerSymmetric tau k hlambda)
    (fun k lambda hlambda =>
      G.vacuumOrthogonalContinuumTaylorResolvent_iteratedDeriv
        T hP hInnerSymmetric hSelf k hlambda)

/-- Direct physical statement: every actual iterated derivative of the
finite-time resolvents converges strongly to the corresponding derivative of
the continuum excitation resolvent. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectTaylorResolvent_iteratedDeriv_tendsto_continuum
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (k : ℕ) {lambda : ℝ} (hlambda : lambda < G.mass / 2)
    (x : P.VacuumOrthogonalHilbert) :
    Tendsto
      (fun tau : G.AdmissibleRescaledDefectTime =>
        (iteratedDeriv k
          (G.admissibleRescaledDefectTaylorResolvent
            T hInnerSymmetric tau) lambda) x)
      G.admissibleRescaledDefectTimeFilter
      (𝓝
        ((iteratedDeriv k
          (G.vacuumOrthogonalContinuumTaylorResolvent
            T hP hInnerSymmetric hSelf) lambda) x)) :=
  (G.canonicalRescaledDefectTaylorStrongLimitData
    T hP hInnerSymmetric hSelf).iteratedDeriv_tendsto_apply
      k hlambda x

/-- Physical package combining all-order Taylor strong convergence with the
already established canonical Hamiltonian graph limit. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorAndGraphLimitPackage
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) :
    (∀ tau : G.AdmissibleRescaledDefectTime,
      ContDiffOn ℝ ∞
        (G.admissibleRescaledDefectTaylorResolvent
          T hInnerSymmetric tau) (Set.Iio (G.mass / 2))) ∧
    ContDiffOn ℝ ∞
      (G.vacuumOrthogonalContinuumTaylorResolvent
        T hP hInnerSymmetric hSelf) (Set.Iio (G.mass / 2)) ∧
    (∀ k : ℕ, ∀ {lambda : ℝ}, lambda < G.mass / 2 →
      ∀ x : P.VacuumOrthogonalHilbert,
        Tendsto
          (fun tau : G.AdmissibleRescaledDefectTime =>
            (iteratedDeriv k
              (G.admissibleRescaledDefectTaylorResolvent
                T hInnerSymmetric tau) lambda) x)
          G.admissibleRescaledDefectTimeFilter
          (𝓝
            ((iteratedDeriv k
              (G.vacuumOrthogonalContinuumTaylorResolvent
                T hP hInnerSymmetric hSelf) lambda) x))) ∧
    (FilterSet.kuratowskiInnerLimit G.admissibleRescaledDefectTimeFilter
          (G.rescaledDefectGraphFamily T hInnerSymmetric
            (fun tau : G.AdmissibleRescaledDefectTime => tau)) =
        G.continuumHamiltonianGraph T hSelf ∧
      FilterSet.kuratowskiOuterLimit G.admissibleRescaledDefectTimeFilter
          (G.rescaledDefectGraphFamily T hInnerSymmetric
            (fun tau : G.AdmissibleRescaledDefectTime => tau)) =
        G.continuumHamiltonianGraph T hSelf) := by
  refine ⟨?_, ?_, ?_,
    (G.canonicalRescaledDefectOperatorLimitPackage
      T hP hInnerSymmetric hSelf).2⟩
  · intro tau
    exact
      (G.admissibleRescaledDefectOpenResolventData
        T hInnerSymmetric tau).contDiffOn_infty
  · exact
      (G.vacuumOrthogonalContinuumOpenResolventData
        T hP hInnerSymmetric hSelf).contDiffOn_infty
  · intro k lambda hlambda x
    exact
      G.admissibleRescaledDefectTaylorResolvent_iteratedDeriv_tendsto_continuum
        T hP hInnerSymmetric hSelf k hlambda x

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end MathlibAnalytic
end MGAP4D
