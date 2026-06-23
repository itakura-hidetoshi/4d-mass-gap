import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSClosedRightHamiltonianSurjective
import Mathlib.Analysis.InnerProductSpace.LinearPMap
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

/-- A symmetric closed right Hamiltonian is self-adjoint once its positive
shift is surjective.

The proof uses Mathlib's partially defined adjoint directly.  Symmetry gives
`H̄ ≤ H̄†`.  For a vector in the adjoint domain, surjectivity of `I + H̄`
produces a comparison vector in `D(H̄)`.  Their difference is orthogonal to
the range of `I + H̄`; surjectivity then makes it orthogonal to itself, hence
zero.  This proves the reverse domain inclusion and therefore
`H̄† = H̄`. -/
theorem closedRightHamiltonian_isSelfAdjoint_of_isFormalAdjoint
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric :
      T.closedRightHamiltonian.IsFormalAdjoint
        T.closedRightHamiltonian) :
    IsSelfAdjoint T.closedRightHamiltonian := by
  let A := T.closedRightHamiltonian
  have hDense : Dense (A.domain : Set P.PhysicalHilbert) := by
    simpa [A] using T.closedRightHamiltonian_dense_domain
  have hSymmetricA : A.IsFormalAdjoint A := by
    simpa [A] using hSymmetric
  have hA_le_adjoint : A ≤ A.adjoint :=
    hSymmetricA.le_adjoint hDense
  have hAdjoint_le_A : A.adjoint ≤ A := by
    refine ⟨?_, ?_⟩
    · intro x hx
      let xAdjoint : A.adjoint.domain := ⟨x, hx⟩
      obtain ⟨u, hu⟩ :=
        T.closedRightHamiltonianShift_surjective
          (lambda := (1 : ℝ)) zero_lt_one
          (x + A.adjoint xAdjoint)
      have hu' :
          (u : P.PhysicalHilbert) + A u =
            x + A.adjoint xAdjoint := by
        simpa only [A, T.closedRightHamiltonianShift_apply, one_smul] using hu
      let w : P.PhysicalHilbert := x - (u : P.PhysicalHilbert)
      have horthogonal
          (v : A.domain) :
          inner ℝ (T.closedRightHamiltonianShift 1 v) w = 0 := by
        have hAdjointPairing :
            inner ℝ (A v) x =
              inner ℝ (v : P.PhysicalHilbert) (A.adjoint xAdjoint) := by
          calc
            inner ℝ (A v) x = inner ℝ x (A v) :=
              real_inner_comm _ _
            _ = inner ℝ (A.adjoint xAdjoint)
                (v : P.PhysicalHilbert) := by
              symm
              exact (LinearPMap.adjoint_isFormalAdjoint hDense) xAdjoint v
            _ = inner ℝ (v : P.PhysicalHilbert)
                (A.adjoint xAdjoint) :=
              real_inner_comm _ _
        have hSymmetricPairing :
            inner ℝ (A v) (u : P.PhysicalHilbert) =
              inner ℝ (v : P.PhysicalHilbert) (A u) :=
          hSymmetricA v u
        calc
          inner ℝ (T.closedRightHamiltonianShift 1 v) w =
              (inner ℝ (v : P.PhysicalHilbert) x -
                  inner ℝ (v : P.PhysicalHilbert) (u : P.PhysicalHilbert)) +
                (inner ℝ (A v) x -
                  inner ℝ (A v) (u : P.PhysicalHilbert)) := by
            simp only [w, T.closedRightHamiltonianShift_apply, one_smul,
              inner_add_left, inner_sub_right]
          _ =
              (inner ℝ (v : P.PhysicalHilbert) x -
                  inner ℝ (v : P.PhysicalHilbert) (u : P.PhysicalHilbert)) +
                (inner ℝ (v : P.PhysicalHilbert) (A.adjoint xAdjoint) -
                  inner ℝ (v : P.PhysicalHilbert) (A u)) := by
            rw [hAdjointPairing, hSymmetricPairing]
          _ = inner ℝ (v : P.PhysicalHilbert)
              ((x + A.adjoint xAdjoint) -
                ((u : P.PhysicalHilbert) + A u)) := by
            simp only [inner_sub_right, inner_add_right]
            ring
          _ = 0 := by
            rw [← hu', sub_self, inner_zero_right]
      have hself : inner ℝ w w = 0 := by
        obtain ⟨v, hv⟩ :=
          T.closedRightHamiltonianShift_surjective
            (lambda := (1 : ℝ)) zero_lt_one w
        have hvOrthogonal := horthogonal v
        rw [hv] at hvOrthogonal
        exact hvOrthogonal
      have hnormSq : ‖w‖ ^ 2 = 0 := by
        simpa only [real_inner_self_eq_norm_sq] using hself
      have hnorm : ‖w‖ = 0 := by
        nlinarith [norm_nonneg w]
      have hw : x = (u : P.PhysicalHilbert) := by
        apply sub_eq_zero.mp
        exact norm_eq_zero.mp hnorm
      exact hw.symm ▸ u.property
    · intro x y hxy
      exact (hA_le_adjoint.2 hxy.symm).symm
  rw [LinearPMap.isSelfAdjoint_def]
  exact le_antisymm hAdjoint_le_A hA_le_adjoint

/-- The self-adjointness frontier is now isolated exactly as symmetry of the
closed OS Hamiltonian.  All remaining maximal-accretive input is discharged by
the finite-time Laplace resolvent construction. -/
theorem closedRightHamiltonian_selfAdjoint_iff_isFormalAdjoint
    (T : P.StronglyContinuousPhysicalSemigroup) :
    IsSelfAdjoint T.closedRightHamiltonian ↔
      T.closedRightHamiltonian.IsFormalAdjoint
        T.closedRightHamiltonian := by
  constructor
  · intro hSelf
    rw [LinearPMap.isSelfAdjoint_def] at hSelf
    simpa only [hSelf] using
      (LinearPMap.adjoint_isFormalAdjoint
        T.closedRightHamiltonian_dense_domain)
  · exact T.closedRightHamiltonian_isSelfAdjoint_of_isFormalAdjoint

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
