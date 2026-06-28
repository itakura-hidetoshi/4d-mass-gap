import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumOrthogonalRealResolventAnalytic
import Mathlib.Tactic

noncomputable section

open Set Filter Topology
open scoped InnerProductSpace LinearPMap

namespace LinearPMap

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The real resolvent of a self-adjoint operator is symmetric below a Rayleigh
threshold. -/
theorem realResolvent_inner_left_eq_inner_right
    (A : E →ₗ.[ℝ] E) {mass lambda : ℝ}
    (hSelf : IsSelfAdjoint A)
    (hlambda : lambda < mass)
    (hgap : ∀ x : A.domain,
      mass * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E))
    (y z : E) :
    inner ℝ (A.realResolvent hSelf hlambda hgap y) z =
      inner ℝ y (A.realResolvent hSelf hlambda hgap z) := by
  let x : A.domain :=
    (A.realShiftLinearEquiv hSelf hlambda hgap).symm y
  let w : A.domain :=
    (A.realShiftLinearEquiv hSelf hlambda hgap).symm z
  have hx : A.realShift lambda x = y := by
    simpa [x] using
      A.realShift_realResolvent_preimage hSelf hlambda hgap y
  have hw : A.realShift lambda w = z := by
    simpa [w] using
      A.realShift_realResolvent_preimage hSelf hlambda hgap z
  have hFormal : A.IsFormalAdjoint A := by
    have hAdjoint : A.adjoint.IsFormalAdjoint A :=
      A.adjoint_isFormalAdjoint hSelf.dense_domain
    simpa only [(LinearPMap.isSelfAdjoint_def).mp hSelf] using hAdjoint
  have hcore : inner ℝ (x : E) z = inner ℝ y (w : E) := by
    rw [← hw, ← hx]
    simp only [realShift_apply, inner_sub_right, inner_sub_left,
      real_inner_smul_right, real_inner_smul_left]
    rw [hFormal x w]
  simpa only [realResolvent_apply, x, w] using hcore

/-- The resolvent quadratic form controls the squared norm of the resolved
vector by the distance from the parameter to the Rayleigh threshold. -/
theorem realResolvent_inner_self_ge
    (A : E →ₗ.[ℝ] E) {mass lambda : ℝ}
    (hSelf : IsSelfAdjoint A)
    (hlambda : lambda < mass)
    (hgap : ∀ x : A.domain,
      mass * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E))
    (y : E) :
    (mass - lambda) * ‖A.realResolvent hSelf hlambda hgap y‖ ^ 2 ≤
      inner ℝ (A.realResolvent hSelf hlambda hgap y) y := by
  let x : A.domain :=
    (A.realShiftLinearEquiv hSelf hlambda hgap).symm y
  have hx : A.realShift lambda x = y := by
    simpa [x] using
      A.realShift_realResolvent_preimage hSelf hlambda hgap y
  have hgapx := hgap x
  have hcore :
      (mass - lambda) * ‖(x : E)‖ ^ 2 ≤ inner ℝ (x : E) y := by
    calc
      (mass - lambda) * ‖(x : E)‖ ^ 2 ≤
          inner ℝ (A x) (x : E) - lambda * ‖(x : E)‖ ^ 2 := by
        linarith
      _ = inner ℝ (A.realShift lambda x) (x : E) := by
        simp only [realShift_apply, inner_sub_left, real_inner_smul_left,
          real_inner_self_eq_norm_sq]
      _ = inner ℝ (x : E) (A.realShift lambda x) :=
        real_inner_comm _ _
      _ = inner ℝ (x : E) y := by rw [hx]
  simpa only [realResolvent_apply, x] using hcore

/-- Every real resolvent below a self-adjoint Rayleigh threshold is a positive
operator in quadratic-form sense. -/
theorem realResolvent_inner_self_nonneg
    (A : E →ₗ.[ℝ] E) {mass lambda : ℝ}
    (hSelf : IsSelfAdjoint A)
    (hlambda : lambda < mass)
    (hgap : ∀ x : A.domain,
      mass * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E))
    (y : E) :
    0 ≤ inner ℝ (A.realResolvent hSelf hlambda hgap y) y := by
  calc
    0 ≤ (mass - lambda) *
        ‖A.realResolvent hSelf hlambda hgap y‖ ^ 2 :=
      mul_nonneg (sub_nonneg.mpr hlambda.le) (sq_nonneg _)
    _ ≤ inner ℝ (A.realResolvent hSelf hlambda hgap y) y :=
      A.realResolvent_inner_self_ge hSelf hlambda hgap y

/-- The positive resolvent quadratic form is bounded above by the inverse
spectral distance times the input norm squared. -/
theorem realResolvent_inner_self_le
    (A : E →ₗ.[ℝ] E) {mass lambda : ℝ}
    (hSelf : IsSelfAdjoint A)
    (hlambda : lambda < mass)
    (hgap : ∀ x : A.domain,
      mass * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E))
    (y : E) :
    inner ℝ (A.realResolvent hSelf hlambda hgap y) y ≤
      (mass - lambda)⁻¹ * ‖y‖ ^ 2 := by
  have hnorm :
      ‖A.realResolvent hSelf hlambda hgap y‖ ≤
        (mass - lambda)⁻¹ * ‖y‖ := by
    simpa only [realResolvent_apply, realResolventLinearMap_apply] using
      A.realResolventLinearMap_norm_bound hSelf hlambda hgap y
  calc
    inner ℝ (A.realResolvent hSelf hlambda hgap y) y ≤
        ‖A.realResolvent hSelf hlambda hgap y‖ * ‖y‖ :=
      real_inner_le_norm _ _
    _ ≤ ((mass - lambda)⁻¹ * ‖y‖) * ‖y‖ :=
      mul_le_mul_of_nonneg_right hnorm (norm_nonneg y)
    _ = (mass - lambda)⁻¹ * ‖y‖ ^ 2 := by ring

end LinearPMap

namespace MGAP4D
namespace MathlibAnalytic

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- Symmetry of the vacuum-orthogonal Yang--Mills resolvent. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolvent_symmetric
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ} (hlambda : lambda < G.mass)
    (y z : P.VacuumOrthogonalHilbert) :
    inner ℝ (G.vacuumOrthogonalRealResolvent T hP hSelf hlambda y) z =
      inner ℝ y
        (G.vacuumOrthogonalRealResolvent T hP hSelf hlambda z) := by
  apply LinearPMap.realResolvent_inner_left_eq_inner_right
    (A := T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf)
    (hSelf :=
      T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint_isSelfAdjoint
        hP hSelf)
    hlambda

/-- Coercive quadratic-form estimate for the vacuum-orthogonal Yang--Mills
resolvent. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolvent_inner_self_ge
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ} (hlambda : lambda < G.mass)
    (y : P.VacuumOrthogonalHilbert) :
    (G.mass - lambda) *
        ‖G.vacuumOrthogonalRealResolvent T hP hSelf hlambda y‖ ^ 2 ≤
      inner ℝ (G.vacuumOrthogonalRealResolvent T hP hSelf hlambda y) y := by
  apply LinearPMap.realResolvent_inner_self_ge
    (A := T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf)
    (hSelf :=
      T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint_isSelfAdjoint
        hP hSelf)
    hlambda

/-- Positivity of the vacuum-orthogonal Yang--Mills resolvent. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolvent_inner_self_nonneg
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ} (hlambda : lambda < G.mass)
    (y : P.VacuumOrthogonalHilbert) :
    0 ≤ inner ℝ
      (G.vacuumOrthogonalRealResolvent T hP hSelf hlambda y) y := by
  apply LinearPMap.realResolvent_inner_self_nonneg
    (A := T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf)
    (hSelf :=
      T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint_isSelfAdjoint
        hP hSelf)
    hlambda

/-- Sharp upper bound for the positive vacuum-orthogonal resolvent quadratic
form. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolvent_inner_self_le
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ} (hlambda : lambda < G.mass)
    (y : P.VacuumOrthogonalHilbert) :
    inner ℝ (G.vacuumOrthogonalRealResolvent T hP hSelf hlambda y) y ≤
      (G.mass - lambda)⁻¹ * ‖y‖ ^ 2 := by
  apply LinearPMap.realResolvent_inner_self_le
    (A := T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf)
    (hSelf :=
      T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint_isSelfAdjoint
        hP hSelf)
    hlambda

/-- Symmetric positive resolvent package below the transferred Yang--Mills mass. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolventPositive_package
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ} (hlambda : lambda < G.mass) :
    (∀ y z : P.VacuumOrthogonalHilbert,
      inner ℝ (G.vacuumOrthogonalRealResolvent T hP hSelf hlambda y) z =
        inner ℝ y
          (G.vacuumOrthogonalRealResolvent T hP hSelf hlambda z)) ∧
      (∀ y : P.VacuumOrthogonalHilbert,
        0 ≤ inner ℝ
          (G.vacuumOrthogonalRealResolvent T hP hSelf hlambda y) y) ∧
      ∀ y : P.VacuumOrthogonalHilbert,
        (G.mass - lambda) *
            ‖G.vacuumOrthogonalRealResolvent T hP hSelf hlambda y‖ ^ 2 ≤
          inner ℝ
            (G.vacuumOrthogonalRealResolvent T hP hSelf hlambda y) y ∧
        inner ℝ
            (G.vacuumOrthogonalRealResolvent T hP hSelf hlambda y) y ≤
          (G.mass - lambda)⁻¹ * ‖y‖ ^ 2 := by
  refine ⟨G.vacuumOrthogonalRealResolvent_symmetric T hP hSelf hlambda,
    G.vacuumOrthogonalRealResolvent_inner_self_nonneg T hP hSelf hlambda, ?_⟩
  intro y
  exact ⟨G.vacuumOrthogonalRealResolvent_inner_self_ge T hP hSelf hlambda y,
    G.vacuumOrthogonalRealResolvent_inner_self_le T hP hSelf hlambda y⟩

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end MathlibAnalytic
end MGAP4D

end
