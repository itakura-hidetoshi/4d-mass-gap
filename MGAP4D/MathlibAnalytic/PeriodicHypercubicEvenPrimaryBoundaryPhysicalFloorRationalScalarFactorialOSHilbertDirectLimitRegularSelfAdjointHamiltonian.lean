import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitRegularHamiltonianLaplaceResolvent
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Tactic

/-!
# Self-adjoint realization of the same-root regular OS Hamiltonian

The canonical graph-closed Hamiltonian is densely defined, formally symmetric and nonnegative, and
every positive shift is surjective by the finite-Laplace resolvent construction.  Surjectivity of
`I + H̄` gives the reverse inclusion of the adjoint domain, so Mathlib's partially defined adjoint
identifies the closed Hamiltonian with its adjoint.

This file stops exactly at self-adjointness and the positive-shift resolvent package.  The spectral
functional calculus identification `T_t = exp(-t H̄)` remains the next package.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter Set Topology
open scoped InnerProductSpace LinearPMap

noncomputable section

namespace PrimaryScalarFixedSlotOSPreHilbertData

variable {H : ℕ → ℕ}
variable {N : ℕ} {hN : 0 < N}
variable [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
variable {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable {L :
  PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
    H N hN beta hbeta
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing}

/-- The canonical graph-closed same-root OS Hamiltonian is self-adjoint. -/
theorem fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_isSelfAdjoint
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    IsSelfAdjoint P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian := by
  let A := P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian
  have hDense : Dense (A.domain : Set P.fixedSlotHilbertDirectLimitRegularSubspace) := by
    simpa [A] using P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_dense_domain
  have hSymmetricA : A.IsFormalAdjoint A := by
    simpa [A] using P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_isFormalAdjoint
  have hA_le_adjoint : A ≤ A.adjoint :=
    hSymmetricA.le_adjoint hDense
  have hAdjoint_le_A : A.adjoint ≤ A := by
    refine ⟨?_, ?_⟩
    · intro x hx
      let xAdjoint : A.adjoint.domain := ⟨x, hx⟩
      obtain ⟨u, hu⟩ :=
        P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift_surjective
          (lambda := (1 : ℝ)) zero_lt_one
          (x + A.adjoint xAdjoint)
      have hu' :
          (u : P.fixedSlotHilbertDirectLimitRegularSubspace) + A u =
            x + A.adjoint xAdjoint := by
        simpa only [A,
          P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift_apply,
          one_smul] using hu
      let w : P.fixedSlotHilbertDirectLimitRegularSubspace :=
        x - (u : P.fixedSlotHilbertDirectLimitRegularSubspace)
      have horthogonal (v : A.domain) :
          inner ℝ
            (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift 1 v) w = 0 := by
        have hAdjointPairing :
            inner ℝ (A v) x =
              inner ℝ (v : P.fixedSlotHilbertDirectLimitRegularSubspace)
                (A.adjoint xAdjoint) := by
          calc
            inner ℝ (A v) x = inner ℝ x (A v) := real_inner_comm _ _
            _ = inner ℝ (A.adjoint xAdjoint)
                (v : P.fixedSlotHilbertDirectLimitRegularSubspace) := by
              symm
              exact (LinearPMap.adjoint_isFormalAdjoint hDense) xAdjoint v
            _ = inner ℝ (v : P.fixedSlotHilbertDirectLimitRegularSubspace)
                (A.adjoint xAdjoint) := real_inner_comm _ _
        have hSymmetricPairing :
            inner ℝ (A v) (u : P.fixedSlotHilbertDirectLimitRegularSubspace) =
              inner ℝ (v : P.fixedSlotHilbertDirectLimitRegularSubspace) (A u) :=
          hSymmetricA v u
        calc
          inner ℝ
              (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift 1 v) w =
              (inner ℝ (v : P.fixedSlotHilbertDirectLimitRegularSubspace) x -
                  inner ℝ (v : P.fixedSlotHilbertDirectLimitRegularSubspace)
                    (u : P.fixedSlotHilbertDirectLimitRegularSubspace)) +
                (inner ℝ (A v) x -
                  inner ℝ (A v) (u : P.fixedSlotHilbertDirectLimitRegularSubspace)) := by
            simp only [A, w,
              P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift_apply,
              one_smul, inner_add_left, inner_sub_right]
            ring
          _ =
              (inner ℝ (v : P.fixedSlotHilbertDirectLimitRegularSubspace) x -
                  inner ℝ (v : P.fixedSlotHilbertDirectLimitRegularSubspace)
                    (u : P.fixedSlotHilbertDirectLimitRegularSubspace)) +
                (inner ℝ (v : P.fixedSlotHilbertDirectLimitRegularSubspace)
                    (A.adjoint xAdjoint) -
                  inner ℝ (v : P.fixedSlotHilbertDirectLimitRegularSubspace) (A u)) := by
            rw [hAdjointPairing, hSymmetricPairing]
          _ = inner ℝ (v : P.fixedSlotHilbertDirectLimitRegularSubspace)
              ((x + A.adjoint xAdjoint) -
                ((u : P.fixedSlotHilbertDirectLimitRegularSubspace) + A u)) := by
            simp only [inner_sub_right, inner_add_right]
            ring
          _ = 0 := by
            rw [← hu', sub_self, inner_zero_right]
      have hself : inner ℝ w w = 0 := by
        obtain ⟨v, hv⟩ :=
          P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift_surjective
            (lambda := (1 : ℝ)) zero_lt_one w
        have hvOrthogonal := horthogonal v
        rw [hv] at hvOrthogonal
        exact hvOrthogonal
      have hnormSq : ‖w‖ ^ 2 = 0 := by
        simpa only [real_inner_self_eq_norm_sq] using hself
      have hnorm : ‖w‖ = 0 := by
        nlinarith [norm_nonneg w]
      have hw : x = (u : P.fixedSlotHilbertDirectLimitRegularSubspace) := by
        apply sub_eq_zero.mp
        exact norm_eq_zero.mp hnorm
      exact hw.symm ▸ u.property
    · intro x y hxy
      exact (hA_le_adjoint.2 hxy.symm).symm
  rw [LinearPMap.isSelfAdjoint_def]
  exact le_antisymm hAdjoint_le_A hA_le_adjoint

/-- Collected closed Hamiltonian package: closedness, dense domain, nonnegative quadratic form,
all positive-shift bijections, and self-adjointness. -/
theorem fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_selfAdjoint_resolvent_package
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    LinearPMap.IsClosed P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian ∧
      Dense ((P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain :
        Set P.fixedSlotHilbertDirectLimitRegularSubspace)) ∧
      (∀ x : P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain,
        0 ≤ inner ℝ (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian x)
          (x : P.fixedSlotHilbertDirectLimitRegularSubspace)) ∧
      (∀ lambda : ℝ, 0 < lambda →
        Function.Bijective
          (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift lambda)) ∧
      IsSelfAdjoint P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian := by
  exact ⟨P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_isClosed,
    P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_dense_domain,
    P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_inner_nonneg,
    fun _ hlambda =>
      P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift_bijective hlambda,
    P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_isSelfAdjoint⟩

end PrimaryScalarFixedSlotOSPreHilbertData

end
end MathlibAnalytic
end MGAP4D
