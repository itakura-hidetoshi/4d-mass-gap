import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumOrthogonalContinuousRealResolvent
import Mathlib.Tactic

noncomputable section

open Set Filter Topology
open scoped InnerProductSpace LinearPMap

namespace LinearPMap

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Changing the real shift parameter changes the shifted value by the
corresponding scalar multiple of the domain vector. -/
theorem realShift_change_parameter
    (A : E →ₗ.[ℝ] E) (lambda mu : ℝ) (x : A.domain) :
    A.realShift lambda x =
      A.realShift mu x + (mu - lambda) • (x : E) := by
  simp only [realShift_apply]
  module

/-- Pointwise real resolvent identity below a common Rayleigh threshold. -/
theorem realResolvent_sub_apply
    (A : E →ₗ.[ℝ] E) {mass lambda mu : ℝ}
    (hSelf : IsSelfAdjoint A)
    (hlambda : lambda < mass)
    (hmu : mu < mass)
    (hgap : ∀ x : A.domain,
      mass * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E))
    (y : E) :
    A.realResolvent hSelf hlambda hgap y -
        A.realResolvent hSelf hmu hgap y =
      (lambda - mu) •
        A.realResolvent hSelf hlambda hgap
          (A.realResolvent hSelf hmu hgap y) := by
  let xlambda : A.domain :=
    (A.realShiftLinearEquiv hSelf hlambda hgap).symm y
  let xmu : A.domain :=
    (A.realShiftLinearEquiv hSelf hmu hgap).symm y
  let xlambdaMu : A.domain :=
    (A.realShiftLinearEquiv hSelf hlambda hgap).symm (xmu : E)
  have hxlambda : A.realShift lambda xlambda = y := by
    simpa [xlambda] using
      A.realShift_realResolvent_preimage hSelf hlambda hgap y
  have hxmu : A.realShift mu xmu = y := by
    simpa [xmu] using
      A.realShift_realResolvent_preimage hSelf hmu hgap y
  have hxlambdaMu : A.realShift lambda xlambdaMu = (xmu : E) := by
    simpa [xlambdaMu] using
      A.realShift_realResolvent_preimage hSelf hlambda hgap (xmu : E)
  have hxmuAtLambda :
      A.realShift lambda xmu = y + (mu - lambda) • (xmu : E) := by
    calc
      A.realShift lambda xmu =
          A.realShift mu xmu + (mu - lambda) • (xmu : E) :=
        A.realShift_change_parameter lambda mu xmu
      _ = y + (mu - lambda) • (xmu : E) := by rw [hxmu]
  have hcandidate :
      A.realShift lambda (xmu + (lambda - mu) • xlambdaMu) = y := by
    rw [map_add, map_smul, hxmuAtLambda, hxlambdaMu]
    module
  have hdomain :
      xlambda = xmu + (lambda - mu) • xlambdaMu := by
    apply A.realShift_injective hlambda hgap
    exact hxlambda.trans hcandidate.symm
  have hambient :
      (xlambda : E) - (xmu : E) =
        (lambda - mu) • (xlambdaMu : E) := by
    rw [hdomain]
    simp
  simpa [xlambda, xmu, xlambdaMu] using hambient

/-- The real resolvent identity as an equality of continuous linear maps. -/
theorem realResolvent_sub_eq_smul_comp
    (A : E →ₗ.[ℝ] E) {mass lambda mu : ℝ}
    (hSelf : IsSelfAdjoint A)
    (hlambda : lambda < mass)
    (hmu : mu < mass)
    (hgap : ∀ x : A.domain,
      mass * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E)) :
    A.realResolvent hSelf hlambda hgap -
        A.realResolvent hSelf hmu hgap =
      (lambda - mu) •
        ((A.realResolvent hSelf hlambda hgap).comp
          (A.realResolvent hSelf hmu hgap)) := by
  ext y
  exact A.realResolvent_sub_apply hSelf hlambda hmu hgap y

/-- Two-parameter quantitative continuity estimate for the real resolvent. -/
theorem realResolvent_sub_norm_le
    (A : E →ₗ.[ℝ] E) {mass lambda mu : ℝ}
    (hSelf : IsSelfAdjoint A)
    (hlambda : lambda < mass)
    (hmu : mu < mass)
    (hgap : ∀ x : A.domain,
      mass * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E)) :
    ‖A.realResolvent hSelf hlambda hgap -
        A.realResolvent hSelf hmu hgap‖ ≤
      |lambda - mu| *
        ((mass - lambda)⁻¹ * (mass - mu)⁻¹) := by
  apply ContinuousLinearMap.opNorm_le_bound
  · positivity
  · intro y
    change
      ‖A.realResolvent hSelf hlambda hgap y -
          A.realResolvent hSelf hmu hgap y‖ ≤
        (|lambda - mu| *
            ((mass - lambda)⁻¹ * (mass - mu)⁻¹)) * ‖y‖
    rw [A.realResolvent_sub_apply hSelf hlambda hmu hgap y,
      norm_smul, Real.norm_eq_abs]
    have hlambdaBound :
        ‖A.realResolvent hSelf hlambda hgap
            (A.realResolvent hSelf hmu hgap y)‖ ≤
          (mass - lambda)⁻¹ *
            ‖A.realResolvent hSelf hmu hgap y‖ := by
      simpa only [realResolvent_apply, realResolventLinearMap_apply] using
        A.realResolventLinearMap_norm_bound hSelf hlambda hgap
          (A.realResolvent hSelf hmu hgap y)
    have hmuBound :
        ‖A.realResolvent hSelf hmu hgap y‖ ≤
          (mass - mu)⁻¹ * ‖y‖ := by
      simpa only [realResolvent_apply, realResolventLinearMap_apply] using
        A.realResolventLinearMap_norm_bound hSelf hmu hgap y
    have hlambdaInv : 0 ≤ (mass - lambda)⁻¹ :=
      inv_nonneg.mpr (sub_nonneg.mpr hlambda.le)
    calc
      |lambda - mu| *
          ‖A.realResolvent hSelf hlambda hgap
            (A.realResolvent hSelf hmu hgap y)‖ ≤
        |lambda - mu| *
          ((mass - lambda)⁻¹ *
            ‖A.realResolvent hSelf hmu hgap y‖) :=
        mul_le_mul_of_nonneg_left hlambdaBound (abs_nonneg _)
      _ ≤ |lambda - mu| *
          ((mass - lambda)⁻¹ * ((mass - mu)⁻¹ * ‖y‖)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hmuBound hlambdaInv)
          (abs_nonneg _)
      _ = (|lambda - mu| *
          ((mass - lambda)⁻¹ * (mass - mu)⁻¹)) * ‖y‖ := by
        ring

end LinearPMap

namespace MGAP4D
namespace MathlibAnalytic

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- Pointwise resolvent identity on the vacuum-orthogonal excitation sector. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolvent_sub_apply
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda mu : ℝ}
    (hlambda : lambda < G.mass)
    (hmu : mu < G.mass)
    (y : P.VacuumOrthogonalHilbert) :
    G.vacuumOrthogonalRealResolvent T hP hSelf hlambda y -
        G.vacuumOrthogonalRealResolvent T hP hSelf hmu y =
      (lambda - mu) •
        G.vacuumOrthogonalRealResolvent T hP hSelf hlambda
          (G.vacuumOrthogonalRealResolvent T hP hSelf hmu y) := by
  apply LinearPMap.realResolvent_sub_apply
    (A := T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf)
    (hSelf :=
      T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint_isSelfAdjoint
        hP hSelf)
    hlambda hmu
  intro z
  simpa only [vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint] using
    G.vacuumOrthogonalClosedRightHamiltonian_gap T hP
      ((T.closedRightHamiltonian_selfAdjoint_iff_isFormalAdjoint).mp hSelf) z

/-- Real resolvent identity as a continuous-linear-map equality on the
vacuum-orthogonal excitation Hilbert space. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolvent_identity
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda mu : ℝ}
    (hlambda : lambda < G.mass)
    (hmu : mu < G.mass) :
    G.vacuumOrthogonalRealResolvent T hP hSelf hlambda -
        G.vacuumOrthogonalRealResolvent T hP hSelf hmu =
      (lambda - mu) •
        ((G.vacuumOrthogonalRealResolvent T hP hSelf hlambda).comp
          (G.vacuumOrthogonalRealResolvent T hP hSelf hmu)) := by
  ext y
  exact G.vacuumOrthogonalRealResolvent_sub_apply
    T hP hSelf hlambda hmu y

/-- Quantitative two-parameter norm control for the excitation resolvent. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolvent_sub_norm_le
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda mu : ℝ}
    (hlambda : lambda < G.mass)
    (hmu : mu < G.mass) :
    ‖G.vacuumOrthogonalRealResolvent T hP hSelf hlambda -
        G.vacuumOrthogonalRealResolvent T hP hSelf hmu‖ ≤
      |lambda - mu| *
        ((G.mass - lambda)⁻¹ * (G.mass - mu)⁻¹) := by
  apply LinearPMap.realResolvent_sub_norm_le
    (A := T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf)
    (hSelf :=
      T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint_isSelfAdjoint
        hP hSelf)
    hlambda hmu
  intro z
  simpa only [vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint] using
    G.vacuumOrthogonalClosedRightHamiltonian_gap T hP
      ((T.closedRightHamiltonian_selfAdjoint_iff_isFormalAdjoint).mp hSelf) z

/-- Resolvent-identity and parameter-control package below the transferred mass. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolventIdentity_package
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda mu : ℝ}
    (hlambda : lambda < G.mass)
    (hmu : mu < G.mass) :
    G.vacuumOrthogonalRealResolvent T hP hSelf hlambda -
          G.vacuumOrthogonalRealResolvent T hP hSelf hmu =
        (lambda - mu) •
          ((G.vacuumOrthogonalRealResolvent T hP hSelf hlambda).comp
            (G.vacuumOrthogonalRealResolvent T hP hSelf hmu)) ∧
      ‖G.vacuumOrthogonalRealResolvent T hP hSelf hlambda -
          G.vacuumOrthogonalRealResolvent T hP hSelf hmu‖ ≤
        |lambda - mu| *
          ((G.mass - lambda)⁻¹ * (G.mass - mu)⁻¹) :=
  ⟨G.vacuumOrthogonalRealResolvent_identity T hP hSelf hlambda hmu,
    G.vacuumOrthogonalRealResolvent_sub_norm_le T hP hSelf hlambda hmu⟩

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end MathlibAnalytic
end MGAP4D

end
