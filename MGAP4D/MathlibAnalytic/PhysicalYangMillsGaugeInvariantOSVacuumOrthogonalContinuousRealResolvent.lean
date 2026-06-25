import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumOrthogonalRealResolventSurjective
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic

noncomputable section

open Set Filter Topology
open scoped InnerProductSpace LinearPMap

namespace LinearPMap

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The algebraic real resolvent below a Rayleigh threshold, viewed in the
ambient Hilbert space rather than in the operator-domain subtype. -/
noncomputable def realResolventLinearMap
    (A : E →ₗ.[ℝ] E) {mass lambda : ℝ}
    (hSelf : IsSelfAdjoint A)
    (hlambda : lambda < mass)
    (hgap : ∀ x : A.domain,
      mass * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E)) :
    E →ₗ[ℝ] E :=
  A.domain.subtype.comp
    (A.realShiftLinearEquiv hSelf hlambda hgap).symm.toLinearMap

@[simp] theorem realResolventLinearMap_apply
    (A : E →ₗ.[ℝ] E) {mass lambda : ℝ}
    (hSelf : IsSelfAdjoint A)
    (hlambda : lambda < mass)
    (hgap : ∀ x : A.domain,
      mass * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E))
    (y : E) :
    A.realResolventLinearMap hSelf hlambda hgap y =
      ((A.realShiftLinearEquiv hSelf hlambda hgap).symm y : E) :=
  rfl

/-- Pointwise resolvent estimate in the standard reciprocal form. -/
theorem realResolventLinearMap_norm_bound
    (A : E →ₗ.[ℝ] E) {mass lambda : ℝ}
    (hSelf : IsSelfAdjoint A)
    (hlambda : lambda < mass)
    (hgap : ∀ x : A.domain,
      mass * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E))
    (y : E) :
    ‖A.realResolventLinearMap hSelf hlambda hgap y‖ ≤
      (mass - lambda)⁻¹ * ‖y‖ := by
  have hbound :=
    A.realShiftLinearEquiv_symm_norm_bound hSelf hlambda hgap y
  have hpositive : 0 < mass - lambda := sub_pos.mpr hlambda
  rw [realResolventLinearMap_apply, inv_mul_eq_div]
  apply (le_div_iff₀ hpositive).2
  simpa [mul_comm] using hbound

/-- The continuous real resolvent below the Rayleigh threshold. -/
noncomputable def realResolvent
    (A : E →ₗ.[ℝ] E) {mass lambda : ℝ}
    (hSelf : IsSelfAdjoint A)
    (hlambda : lambda < mass)
    (hgap : ∀ x : A.domain,
      mass * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E)) :
    E →L[ℝ] E :=
  (A.realResolventLinearMap hSelf hlambda hgap).mkContinuous
    ((mass - lambda)⁻¹)
    (A.realResolventLinearMap_norm_bound hSelf hlambda hgap)

@[simp] theorem realResolvent_apply
    (A : E →ₗ.[ℝ] E) {mass lambda : ℝ}
    (hSelf : IsSelfAdjoint A)
    (hlambda : lambda < mass)
    (hgap : ∀ x : A.domain,
      mass * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E))
    (y : E) :
    A.realResolvent hSelf hlambda hgap y =
      ((A.realShiftLinearEquiv hSelf hlambda hgap).symm y : E) :=
  rfl

/-- The operator norm of the continuous real resolvent is bounded by the
inverse distance to the Rayleigh threshold. -/
theorem realResolvent_norm_le
    (A : E →ₗ.[ℝ] E) {mass lambda : ℝ}
    (hSelf : IsSelfAdjoint A)
    (hlambda : lambda < mass)
    (hgap : ∀ x : A.domain,
      mass * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E)) :
    ‖A.realResolvent hSelf hlambda hgap‖ ≤ (mass - lambda)⁻¹ := by
  apply LinearMap.mkContinuous_norm_le
  · exact inv_nonneg.mpr (sub_nonneg.mpr hlambda.le)
  · exact A.realResolventLinearMap_norm_bound hSelf hlambda hgap

/-- The continuous real resolvent agrees with the unique algebraic shifted
preimage. -/
theorem realShift_realResolvent_preimage
    (A : E →ₗ.[ℝ] E) {mass lambda : ℝ}
    (hSelf : IsSelfAdjoint A)
    (hlambda : lambda < mass)
    (hgap : ∀ x : A.domain,
      mass * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E))
    (y : E) :
    A.realShift lambda
        ((A.realShiftLinearEquiv hSelf hlambda hgap).symm y) = y := by
  change A.realShiftLinearEquiv hSelf hlambda hgap
      ((A.realShiftLinearEquiv hSelf hlambda hgap).symm y) = y
  exact LinearEquiv.apply_symm_apply _ y

end LinearPMap

namespace MGAP4D
namespace MathlibAnalytic

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- The vacuum-orthogonal excitation resolvent as a continuous linear
endomorphism of the complete excitation Hilbert space. -/
noncomputable def FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolvent
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ} (hlambda : lambda < G.mass) :
    P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert :=
  LinearPMap.realResolvent
    (A := T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf)
    (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint_isSelfAdjoint
      hP hSelf)
    hlambda
    (by
      intro y
      simpa only [vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint] using
        G.vacuumOrthogonalClosedRightHamiltonian_gap T hP
          ((T.closedRightHamiltonian_selfAdjoint_iff_isFormalAdjoint).mp hSelf) y)

@[simp] theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolvent_apply
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ} (hlambda : lambda < G.mass)
    (y : P.VacuumOrthogonalHilbert) :
    G.vacuumOrthogonalRealResolvent T hP hSelf hlambda y =
      ((G.vacuumOrthogonalRealShiftLinearEquiv T hP hSelf hlambda).symm y :
        P.VacuumOrthogonalHilbert) := by
  rfl

/-- Sharp pointwise norm estimate for the continuous excitation resolvent. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolvent_norm_bound
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ} (hlambda : lambda < G.mass)
    (y : P.VacuumOrthogonalHilbert) :
    ‖G.vacuumOrthogonalRealResolvent T hP hSelf hlambda y‖ ≤
      (G.mass - lambda)⁻¹ * ‖y‖ := by
  have hbound := G.vacuumOrthogonalRealShift_inverse_norm_bound
    T hP hSelf hlambda y
  have hpositive : 0 < G.mass - lambda := sub_pos.mpr hlambda
  rw [G.vacuumOrthogonalRealResolvent_apply T hP hSelf hlambda,
    inv_mul_eq_div]
  apply (le_div_iff₀ hpositive).2
  simpa [mul_comm] using hbound

/-- Operator norm estimate for the continuous excitation resolvent. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolvent_norm_le
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ} (hlambda : lambda < G.mass) :
    ‖G.vacuumOrthogonalRealResolvent T hP hSelf hlambda‖ ≤
      (G.mass - lambda)⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound
  · exact inv_nonneg.mpr (sub_nonneg.mpr hlambda.le)
  · exact G.vacuumOrthogonalRealResolvent_norm_bound T hP hSelf hlambda

/-- Continuous-resolvent package below the transferred mass. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalContinuousRealResolvent_package
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ} (hlambda : lambda < G.mass) :
    (∃ R : P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert,
        R = G.vacuumOrthogonalRealResolvent T hP hSelf hlambda ∧
        ‖R‖ ≤ (G.mass - lambda)⁻¹) ∧
      Function.Bijective
        (T.vacuumOrthogonalClosedRightHamiltonianRealShift hSelf lambda) :=
  ⟨⟨G.vacuumOrthogonalRealResolvent T hP hSelf hlambda, rfl,
      G.vacuumOrthogonalRealResolvent_norm_le T hP hSelf hlambda⟩,
    G.vacuumOrthogonalRealShift_bijective T hP hSelf hlambda⟩

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end MathlibAnalytic
end MGAP4D

end
