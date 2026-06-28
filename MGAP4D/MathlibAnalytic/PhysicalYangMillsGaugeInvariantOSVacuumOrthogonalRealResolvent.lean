import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumOrthogonalSelfAdjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic

noncomputable section

open Set Filter Topology
open scoped InnerProductSpace LinearPMap

namespace LinearPMap

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The real spectral shift `A - λI`, acting on the domain of `A`. -/
def realShift (A : E →ₗ.[ℝ] E) (lambda : ℝ) : A.domain →ₗ[ℝ] E :=
  A.toFun - lambda • A.domain.subtype

@[simp] theorem realShift_apply
    (A : E →ₗ.[ℝ] E) (lambda : ℝ) (x : A.domain) :
    A.realShift lambda x = A x - lambda • (x : E) := by
  rfl

/-- A Rayleigh lower bound for `A` gives a quantitative norm lower bound for
`A - λI` at every real `λ` below the Rayleigh threshold. -/
theorem realShift_norm_lower_bound
    (A : E →ₗ.[ℝ] E) {mass lambda : ℝ}
    (hlambda : lambda < mass)
    (hgap : ∀ x : A.domain,
      mass * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E))
    (x : A.domain) :
    (mass - lambda) * ‖(x : E)‖ ≤ ‖A.realShift lambda x‖ := by
  by_cases hx : 0 < ‖(x : E)‖
  · refine (mul_le_mul_iff_left₀ hx).mp ?_
    calc
      (mass - lambda) * ‖(x : E)‖ * ‖(x : E)‖ =
          (mass - lambda) * ‖(x : E)‖ ^ 2 := by ring
      _ ≤ inner ℝ (A x) (x : E) - lambda * ‖(x : E)‖ ^ 2 := by
        have hxgap := hgap x
        linarith
      _ = inner ℝ (A.realShift lambda x) (x : E) := by
        simp only [realShift_apply, inner_sub_left, real_inner_smul_left,
          real_inner_self_eq_norm_sq]
      _ ≤ ‖A.realShift lambda x‖ * ‖(x : E)‖ :=
        real_inner_le_norm _ _
  · have hxzero : (x : E) = 0 := by
      exact norm_eq_zero.mp (le_antisymm (le_of_not_gt hx) (norm_nonneg _))
    simp [hxzero]

/-- Below the Rayleigh threshold, the real shift has trivial kernel. -/
theorem realShift_injective
    (A : E →ₗ.[ℝ] E) {mass lambda : ℝ}
    (hlambda : lambda < mass)
    (hgap : ∀ x : A.domain,
      mass * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E)) :
    Function.Injective (A.realShift lambda) := by
  intro x y hxy
  have hbound := A.realShift_norm_lower_bound hlambda hgap (x - y)
  have hshiftZero : A.realShift lambda (x - y) = 0 := by
    calc
      A.realShift lambda (x - y) =
          A.realShift lambda x - A.realShift lambda y :=
        (A.realShift lambda).map_sub x y
      _ = 0 := sub_eq_zero.mpr hxy
  rw [hshiftZero, norm_zero] at hbound
  have hpositive : 0 < mass - lambda := sub_pos.mpr hlambda
  have hnorm : ‖((x - y : A.domain) : E)‖ = 0 := by
    nlinarith [norm_nonneg (((x - y : A.domain) : E))]
  apply Subtype.ext
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

variable [CompleteSpace E]

/-- For a self-adjoint operator bounded below by `mass`, every real shift below
`mass` has dense range.  Orthogonality to the range creates an adjoint-domain
eigenvector at `lambda`; self-adjointness and the Rayleigh bound force it to
vanish. -/
theorem realShift_dense_range
    (A : E →ₗ.[ℝ] E) {mass lambda : ℝ}
    (hSelf : IsSelfAdjoint A)
    (hlambda : lambda < mass)
    (hgap : ∀ x : A.domain,
      mass * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E)) :
    Dense (LinearMap.range (A.realShift lambda) : Set E) := by
  have hOrthogonal :
      (LinearMap.range (A.realShift lambda))ᗮ = (⊥ : Submodule ℝ E) := by
    apply bot_unique
    intro z hz
    have hRangeOrthogonal (x : A.domain) :
        inner ℝ (A.realShift lambda x) z = 0 :=
      hz (A.realShift lambda x) ⟨x, rfl⟩
    have hAdjointPairing (x : A.domain) :
        inner ℝ (lambda • z) (x : E) = inner ℝ z (A x) := by
      have hzero := hRangeOrthogonal x
      simp only [realShift_apply, inner_sub_left, real_inner_smul_left] at hzero
      calc
        inner ℝ (lambda • z) (x : E) =
            lambda * inner ℝ z (x : E) := by
          rw [real_inner_smul_left]
        _ = lambda * inner ℝ (x : E) z := by
          rw [real_inner_comm z (x : E)]
        _ = inner ℝ (A x) z := by linarith
        _ = inner ℝ z (A x) := real_inner_comm _ _
    have hzAdjointDomain : z ∈ A.adjoint.domain :=
      A.mem_adjoint_domain_of_exists z ⟨lambda • z, hAdjointPairing⟩
    let zAdjoint : A.adjoint.domain := ⟨z, hzAdjointDomain⟩
    have hAdjointValue : A.adjoint zAdjoint = lambda • z :=
      A.adjoint_apply_eq hSelf.dense_domain zAdjoint hAdjointPairing
    have hSelfEq : A.adjoint = A :=
      (LinearPMap.isSelfAdjoint_def).mp hSelf
    have hzDomain : z ∈ A.domain := by
      rw [← hSelfEq]
      exact hzAdjointDomain
    let zDomain : A.domain := ⟨z, hzDomain⟩
    have hAdjointLe : A.adjoint ≤ A := le_of_eq hSelfEq
    have hSameValue : A.adjoint zAdjoint = A zDomain :=
      hAdjointLe.2 rfl
    have hEigen : A zDomain = lambda • z :=
      hSameValue.symm.trans hAdjointValue
    have hgapz := hgap zDomain
    rw [hEigen, real_inner_smul_left,
      real_inner_self_eq_norm_sq] at hgapz
    have hnormSq : ‖z‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖z‖]
    have hzZero : z = 0 :=
      norm_eq_zero.mp (sq_eq_zero_iff.mp hnormSq)
    simpa [hzZero]
  rw [dense_iff_closure_eq]
  have hTopologicalClosure :
      (LinearMap.range (A.realShift lambda)).topologicalClosure =
        (⊤ : Submodule ℝ E) :=
    (Submodule.topologicalClosure_eq_top_iff).2 hOrthogonal
  simpa [Submodule.topologicalClosure_coe] using
    congrArg (fun K : Submodule ℝ E => (K : Set E)) hTopologicalClosure

end LinearPMap

namespace MGAP4D
namespace MathlibAnalytic

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- The shifted excitation Hamiltonian below a candidate transferred mass. -/
def vacuumOrthogonalClosedRightHamiltonianRealShift
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (lambda : ℝ) :
    (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf).domain →ₗ[ℝ]
      P.VacuumOrthogonalHilbert :=
  (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf).realShift lambda

@[simp] theorem vacuumOrthogonalClosedRightHamiltonianRealShift_apply
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (lambda : ℝ)
    (x : (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf).domain) :
    T.vacuumOrthogonalClosedRightHamiltonianRealShift hSelf lambda x =
      T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf x -
        lambda • (x : P.VacuumOrthogonalHilbert) :=
  rfl

/-- The transferred finite-volume mass gives the sharp coercive norm estimate
for every real shifted excitation Hamiltonian below that mass. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealShift_norm_lower_bound
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ} (hlambda : lambda < G.mass)
    (x : (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf).domain) :
    (G.mass - lambda) * ‖(x : P.VacuumOrthogonalHilbert)‖ ≤
      ‖T.vacuumOrthogonalClosedRightHamiltonianRealShift hSelf lambda x‖ := by
  apply LinearPMap.realShift_norm_lower_bound
    (A := T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf)
    hlambda
  intro y
  simpa only [vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint] using
    G.vacuumOrthogonalClosedRightHamiltonian_gap T hP
      ((T.closedRightHamiltonian_selfAdjoint_iff_isFormalAdjoint).mp hSelf) y

/-- Every real shift below the transferred mass is injective on the complete
excitation Hilbert carrier. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealShift_injective
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ} (hlambda : lambda < G.mass) :
    Function.Injective
      (T.vacuumOrthogonalClosedRightHamiltonianRealShift hSelf lambda) := by
  apply LinearPMap.realShift_injective
    (A := T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf)
    hlambda
  intro y
  simpa only [vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint] using
    G.vacuumOrthogonalClosedRightHamiltonian_gap T hP
      ((T.closedRightHamiltonian_selfAdjoint_iff_isFormalAdjoint).mp hSelf) y

/-- Every real shift below the transferred mass has dense range in the complete
excitation Hilbert space. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealShift_dense_range
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ} (hlambda : lambda < G.mass) :
    Dense
      (LinearMap.range
        (T.vacuumOrthogonalClosedRightHamiltonianRealShift hSelf lambda) :
          Set P.VacuumOrthogonalHilbert) := by
  apply LinearPMap.realShift_dense_range
    (A := T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf)
    (hSelf :=
      T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint_isSelfAdjoint
        hP hSelf)
    hlambda
  intro y
  simpa only [vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint] using
    G.vacuumOrthogonalClosedRightHamiltonian_gap T hP
      ((T.closedRightHamiltonian_selfAdjoint_iff_isFormalAdjoint).mp hSelf) y

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end MathlibAnalytic
end MGAP4D

end
