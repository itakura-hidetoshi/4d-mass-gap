import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumOrthogonalRealResolventClosedRange
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Tactic

noncomputable section

open Set Filter Topology
open scoped InnerProductSpace LinearPMap

namespace LinearPMap

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A self-adjoint operator with Rayleigh lower bound `mass` has surjective real
shift at every `lambda < mass`.

The shifted range is dense by self-adjointness and closed by graph closedness
plus the coercive estimate, hence it is the whole Hilbert space. -/
theorem realShift_surjective
    (A : E →ₗ.[ℝ] E) {mass lambda : ℝ}
    (hSelf : IsSelfAdjoint A)
    (hlambda : lambda < mass)
    (hgap : ∀ x : A.domain,
      mass * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E)) :
    Function.Surjective (A.realShift lambda) := by
  have hDense := A.realShift_dense_range hSelf hlambda hgap
  have hClosedRange :=
    A.realShift_isClosed_range hSelf.isClosed hlambda hgap
  intro y
  have hyClosure :
      y ∈ _root_.closure (LinearMap.range (A.realShift lambda) : Set E) := by
    rw [hDense.closure_eq]
    exact mem_univ y
  exact
    (hClosedRange.closure_subset_iff.mpr
      (fun z hz => hz)) hyClosure

/-- Below the Rayleigh threshold, the shifted operator is algebraically
bijective. -/
theorem realShift_bijective
    (A : E →ₗ.[ℝ] E) {mass lambda : ℝ}
    (hSelf : IsSelfAdjoint A)
    (hlambda : lambda < mass)
    (hgap : ∀ x : A.domain,
      mass * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E)) :
    Function.Bijective (A.realShift lambda) :=
  ⟨A.realShift_injective hlambda hgap,
    A.realShift_surjective hSelf hlambda hgap⟩

/-- The real shift below the Rayleigh threshold as a linear equivalence from the
operator domain onto the ambient Hilbert space. -/
noncomputable def realShiftLinearEquiv
    (A : E →ₗ.[ℝ] E) {mass lambda : ℝ}
    (hSelf : IsSelfAdjoint A)
    (hlambda : lambda < mass)
    (hgap : ∀ x : A.domain,
      mass * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E)) :
    A.domain ≃ₗ[ℝ] E :=
  LinearEquiv.ofBijective (A.realShift lambda)
    (A.realShift_bijective hSelf hlambda hgap)

@[simp] theorem realShiftLinearEquiv_apply
    (A : E →ₗ.[ℝ] E) {mass lambda : ℝ}
    (hSelf : IsSelfAdjoint A)
    (hlambda : lambda < mass)
    (hgap : ∀ x : A.domain,
      mass * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E))
    (x : A.domain) :
    A.realShiftLinearEquiv hSelf hlambda hgap x = A.realShift lambda x :=
  rfl

/-- Quantitative inverse estimate for the real resolvent below the Rayleigh
threshold. -/
theorem realShiftLinearEquiv_symm_norm_bound
    (A : E →ₗ.[ℝ] E) {mass lambda : ℝ}
    (hSelf : IsSelfAdjoint A)
    (hlambda : lambda < mass)
    (hgap : ∀ x : A.domain,
      mass * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E))
    (y : E) :
    (mass - lambda) *
        ‖((A.realShiftLinearEquiv hSelf hlambda hgap).symm y : E)‖ ≤
      ‖y‖ := by
  have hbound :=
    A.realShift_norm_lower_bound hlambda hgap
      ((A.realShiftLinearEquiv hSelf hlambda hgap).symm y)
  have hright :
      A.realShift lambda
          ((A.realShiftLinearEquiv hSelf hlambda hgap).symm y) = y := by
    change A.realShiftLinearEquiv hSelf hlambda hgap
        ((A.realShiftLinearEquiv hSelf hlambda hgap).symm y) = y
    exact LinearEquiv.apply_symm_apply _ y
  rwa [hright] at hbound

/-- Every target has a unique shifted-domain preimage satisfying the sharp
coercive inverse estimate. -/
theorem realShift_existsUnique_preimage_norm_bound
    (A : E →ₗ.[ℝ] E) {mass lambda : ℝ}
    (hSelf : IsSelfAdjoint A)
    (hlambda : lambda < mass)
    (hgap : ∀ x : A.domain,
      mass * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E))
    (y : E) :
    ∃! x : A.domain,
      A.realShift lambda x = y ∧
        (mass - lambda) * ‖(x : E)‖ ≤ ‖y‖ := by
  let x := (A.realShiftLinearEquiv hSelf hlambda hgap).symm y
  have hx : A.realShift lambda x = y := by
    change A.realShiftLinearEquiv hSelf hlambda hgap x = y
    exact LinearEquiv.apply_symm_apply _ y
  refine ⟨x, ⟨hx, ?_⟩, ?_⟩
  · exact A.realShiftLinearEquiv_symm_norm_bound hSelf hlambda hgap y
  · intro z hz
    apply A.realShift_injective hlambda hgap
    exact hz.1.trans hx.symm

end LinearPMap

namespace MGAP4D
namespace MathlibAnalytic

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- Every excitation-sector real shift below the transferred mass is
surjective. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealShift_surjective
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ} (hlambda : lambda < G.mass) :
    Function.Surjective
      (T.vacuumOrthogonalClosedRightHamiltonianRealShift hSelf lambda) := by
  apply LinearPMap.realShift_surjective
    (A := T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf)
    (hSelf :=
      T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint_isSelfAdjoint
        hP hSelf)
    hlambda
  intro y
  simpa only [vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint] using
    G.vacuumOrthogonalClosedRightHamiltonian_gap T hP
      ((T.closedRightHamiltonian_selfAdjoint_iff_isFormalAdjoint).mp hSelf) y

/-- Every excitation-sector real shift below the transferred mass is
bijective. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealShift_bijective
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ} (hlambda : lambda < G.mass) :
    Function.Bijective
      (T.vacuumOrthogonalClosedRightHamiltonianRealShift hSelf lambda) :=
  ⟨G.vacuumOrthogonalRealShift_injective T hP hSelf hlambda,
    G.vacuumOrthogonalRealShift_surjective T hP hSelf hlambda⟩

/-- The excitation-sector real shift below the transferred mass as a linear
equivalence. -/
noncomputable def FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealShiftLinearEquiv
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ} (hlambda : lambda < G.mass) :
    (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf).domain ≃ₗ[ℝ]
      P.VacuumOrthogonalHilbert :=
  LinearEquiv.ofBijective
    (T.vacuumOrthogonalClosedRightHamiltonianRealShift hSelf lambda)
    (G.vacuumOrthogonalRealShift_bijective T hP hSelf hlambda)

/-- Quantitative inverse estimate on the complete excitation Hilbert space. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealShift_inverse_norm_bound
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ} (hlambda : lambda < G.mass)
    (y : P.VacuumOrthogonalHilbert) :
    (G.mass - lambda) *
        ‖((G.vacuumOrthogonalRealShiftLinearEquiv T hP hSelf hlambda).symm y :
          P.VacuumOrthogonalHilbert)‖ ≤
      ‖y‖ := by
  have hbound :=
    G.vacuumOrthogonalRealShift_norm_lower_bound T hP hSelf hlambda
      ((G.vacuumOrthogonalRealShiftLinearEquiv T hP hSelf hlambda).symm y)
  have hright :
      T.vacuumOrthogonalClosedRightHamiltonianRealShift hSelf lambda
          ((G.vacuumOrthogonalRealShiftLinearEquiv T hP hSelf hlambda).symm y) =
        y := by
    change G.vacuumOrthogonalRealShiftLinearEquiv T hP hSelf hlambda
        ((G.vacuumOrthogonalRealShiftLinearEquiv T hP hSelf hlambda).symm y) = y
    exact LinearEquiv.apply_symm_apply _ y
  rwa [hright] at hbound

/-- Complete real-resolvent package below the transferred mass. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolvent_package
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ} (hlambda : lambda < G.mass) :
    Function.Bijective
        (T.vacuumOrthogonalClosedRightHamiltonianRealShift hSelf lambda) ∧
      IsClosed
        (LinearMap.range
          (T.vacuumOrthogonalClosedRightHamiltonianRealShift hSelf lambda) :
            Set P.VacuumOrthogonalHilbert) ∧
      Dense
        (LinearMap.range
          (T.vacuumOrthogonalClosedRightHamiltonianRealShift hSelf lambda) :
            Set P.VacuumOrthogonalHilbert) :=
  ⟨G.vacuumOrthogonalRealShift_bijective T hP hSelf hlambda,
    G.vacuumOrthogonalRealShift_isClosed_range T hP hSelf hlambda,
    G.vacuumOrthogonalRealShift_dense_range T hP hSelf hlambda⟩

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end MathlibAnalytic
end MGAP4D

end
