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
  rw [map_sub, hxy, sub_self, norm_zero] at hbound
  have hpositive : 0 < mass - lambda := sub_pos.mpr hlambda
  have hnorm : ‖((x - y : A.domain) : E)‖ = 0 := by
    nlinarith [norm_nonneg (((x - y : A.domain) : E))]
  apply Subtype.ext
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

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

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end MathlibAnalytic
end MGAP4D

end
