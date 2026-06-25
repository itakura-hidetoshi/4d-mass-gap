import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumOrthogonalDenseDomain
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Tactic

noncomputable section

open Set
open scoped InnerProductSpace LinearPMap

namespace LinearPMap

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The unit positive shift of a partially defined linear operator. -/
def oneShift (A : E →ₗ.[ℝ] E) : A.domain →ₗ[ℝ] E :=
  A.domain.subtype + A.toFun

@[simp] theorem oneShift_apply
    (A : E →ₗ.[ℝ] E) (x : A.domain) :
    A.oneShift x = (x : E) + A x :=
  rfl

/-- A densely defined symmetric operator is self-adjoint once its unit positive
shift is surjective.

This is the abstract Mathlib form of the standard maximal-symmetric criterion.
The proof compares an adjoint-domain vector with a preimage under `I + A` and
uses surjectivity to annihilate their difference. -/
theorem isSelfAdjoint_of_isFormalAdjoint_of_oneShift_surjective
    (A : E →ₗ.[ℝ] E)
    (hDense : Dense (A.domain : Set E))
    (hSymmetric : A.IsFormalAdjoint A)
    (hSurjective : Function.Surjective A.oneShift) :
    IsSelfAdjoint A := by
  have hA_le_adjoint : A ≤ A.adjoint :=
    hSymmetric.le_adjoint hDense
  have hAdjoint_le_A : A.adjoint ≤ A := by
    refine ⟨?_, ?_⟩
    · intro x hx
      let xAdjoint : A.adjoint.domain := ⟨x, hx⟩
      obtain ⟨u, hu⟩ := hSurjective (x + A.adjoint xAdjoint)
      have hu' :
          (u : E) + A u = x + A.adjoint xAdjoint := by
        simpa only [oneShift_apply] using hu
      let w : E := x - (u : E)
      have horthogonal (v : A.domain) :
          inner ℝ (A.oneShift v) w = 0 := by
        have hAdjointPairing :
            inner ℝ (A v) x =
              inner ℝ (v : E) (A.adjoint xAdjoint) := by
          calc
            inner ℝ (A v) x = inner ℝ x (A v) :=
              real_inner_comm _ _
            _ = inner ℝ (A.adjoint xAdjoint) (v : E) := by
              symm
              exact (LinearPMap.adjoint_isFormalAdjoint hDense)
                xAdjoint v
            _ = inner ℝ (v : E) (A.adjoint xAdjoint) :=
              real_inner_comm _ _
        have hSymmetricPairing :
            inner ℝ (A v) (u : E) =
              inner ℝ (v : E) (A u) :=
          hSymmetric v u
        calc
          inner ℝ (A.oneShift v) w =
              (inner ℝ (v : E) x - inner ℝ (v : E) (u : E)) +
                (inner ℝ (A v) x - inner ℝ (A v) (u : E)) := by
            simp only [oneShift_apply, w, inner_add_left, inner_sub_right]
            ring
          _ =
              (inner ℝ (v : E) x - inner ℝ (v : E) (u : E)) +
                (inner ℝ (v : E) (A.adjoint xAdjoint) -
                  inner ℝ (v : E) (A u)) := by
            rw [hAdjointPairing, hSymmetricPairing]
          _ = inner ℝ (v : E)
              ((x + A.adjoint xAdjoint) - ((u : E) + A u)) := by
            simp only [inner_sub_right, inner_add_right]
            ring
          _ = 0 := by
            rw [← hu', sub_self, inner_zero_right]
      have hself : inner ℝ w w = 0 := by
        obtain ⟨v, hv⟩ := hSurjective w
        have hvOrthogonal := horthogonal v
        rw [hv] at hvOrthogonal
        exact hvOrthogonal
      have hnormSq : ‖w‖ ^ 2 = 0 := by
        simpa only [real_inner_self_eq_norm_sq] using hself
      have hnorm : ‖w‖ = 0 := by
        nlinarith [norm_nonneg w]
      have hw : x = (u : E) := by
        apply sub_eq_zero.mp
        exact norm_eq_zero.mp hnorm
      exact hw.symm ▸ u.property
    · intro x y hxy
      exact (hA_le_adjoint.2 hxy.symm).symm
  rw [LinearPMap.isSelfAdjoint_def]
  exact le_antisymm hAdjoint_le_A hA_le_adjoint

end LinearPMap

namespace MGAP4D
namespace MathlibAnalytic

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- The unit positive shift of the closed Hamiltonian restricted to the physical
excitation Hilbert space. -/
def vacuumOrthogonalClosedRightHamiltonianOneShift
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric :
      T.closedRightHamiltonian.IsFormalAdjoint T.closedRightHamiltonian) :
    (T.vacuumOrthogonalClosedRightHamiltonian hSymmetric).domain →ₗ[ℝ]
      P.VacuumOrthogonalHilbert :=
  (T.vacuumOrthogonalClosedRightHamiltonian hSymmetric).oneShift

@[simp] theorem vacuumOrthogonalClosedRightHamiltonianOneShift_apply
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric :
      T.closedRightHamiltonian.IsFormalAdjoint T.closedRightHamiltonian)
    (x : (T.vacuumOrthogonalClosedRightHamiltonian hSymmetric).domain) :
    T.vacuumOrthogonalClosedRightHamiltonianOneShift hSymmetric x =
      (x : P.VacuumOrthogonalHilbert) +
        T.vacuumOrthogonalClosedRightHamiltonian hSymmetric x :=
  rfl

/-- Ambient resolvent surjectivity descends to the vacuum-orthogonal sector.
The preimage is automatically orthogonal to the vacuum because the Hamiltonian
is symmetric and annihilates the vacuum. -/
theorem vacuumOrthogonalClosedRightHamiltonianOneShift_surjective
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric :
      T.closedRightHamiltonian.IsFormalAdjoint T.closedRightHamiltonian) :
    Function.Surjective
      (T.vacuumOrthogonalClosedRightHamiltonianOneShift hSymmetric) := by
  intro y
  obtain ⟨u, hu⟩ :=
    T.closedRightHamiltonianShift_surjective
      (lambda := (1 : ℝ)) zero_lt_one
      ((y : P.VacuumOrthogonalHilbert) : P.PhysicalHilbert)
  have huAmbient :
      (u : P.PhysicalHilbert) + T.closedRightHamiltonian u =
        ((y : P.VacuumOrthogonalHilbert) : P.PhysicalHilbert) := by
    simpa only [T.closedRightHamiltonianShift_apply, one_smul] using hu
  have hyOrthogonal :
      inner ℝ P.vacuum
          ((y : P.VacuumOrthogonalHilbert) : P.PhysicalHilbert) = 0 :=
    (P.mem_vacuumOrthogonal_iff _).mp y.property
  have hHamiltonianOrthogonal :
      inner ℝ P.vacuum (T.closedRightHamiltonian u) = 0 := by
    calc
      inner ℝ P.vacuum (T.closedRightHamiltonian u) =
          inner ℝ
            (T.closedRightHamiltonian
              T.closedRightHamiltonianVacuumDomainPoint)
            (u : P.PhysicalHilbert) := by
        exact
          (hSymmetric T.closedRightHamiltonianVacuumDomainPoint u).symm
      _ = 0 := by simp
  have huOrthogonal :
      inner ℝ P.vacuum (u : P.PhysicalHilbert) = 0 := by
    have hinner :=
      congrArg (fun z : P.PhysicalHilbert => inner ℝ P.vacuum z)
        huAmbient
    change inner ℝ P.vacuum
        ((u : P.PhysicalHilbert) + T.closedRightHamiltonian u) =
      inner ℝ P.vacuum
        ((y : P.VacuumOrthogonalHilbert) : P.PhysicalHilbert) at hinner
    rw [inner_add_right, hHamiltonianOrthogonal, add_zero,
      hyOrthogonal] at hinner
    exact hinner
  let uExcitation : P.VacuumOrthogonalHilbert :=
    ⟨(u : P.PhysicalHilbert),
      (P.mem_vacuumOrthogonal_iff _).2 huOrthogonal⟩
  let uRestricted :
      (T.vacuumOrthogonalClosedRightHamiltonian hSymmetric).domain :=
    ⟨uExcitation, u.property⟩
  refine ⟨uRestricted, ?_⟩
  apply Subtype.ext
  simpa [vacuumOrthogonalClosedRightHamiltonianOneShift,
    LinearPMap.oneShift_apply] using huAmbient

/-- A dense symmetric excitation-sector restriction is self-adjoint. -/
theorem vacuumOrthogonalClosedRightHamiltonian_isSelfAdjoint_of_dense
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric :
      T.closedRightHamiltonian.IsFormalAdjoint T.closedRightHamiltonian)
    (hDense :
      Dense (((T.vacuumOrthogonalClosedRightHamiltonian hSymmetric).domain :
        Set P.VacuumOrthogonalHilbert))) :
    IsSelfAdjoint (T.vacuumOrthogonalClosedRightHamiltonian hSymmetric) := by
  apply LinearPMap.isSelfAdjoint_of_isFormalAdjoint_of_oneShift_surjective
    (A := T.vacuumOrthogonalClosedRightHamiltonian hSymmetric)
  · exact hDense
  · exact T.vacuumOrthogonalClosedRightHamiltonian_isFormalAdjoint hSymmetric
  · simpa only [vacuumOrthogonalClosedRightHamiltonianOneShift] using
      T.vacuumOrthogonalClosedRightHamiltonianOneShift_surjective hSymmetric

/-- Ambient self-adjointness and vacuum normalization produce a self-adjoint
closed Hamiltonian directly on the complete excitation Hilbert space. -/
theorem vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint_isSelfAdjoint
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) :
    IsSelfAdjoint
      (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf) := by
  unfold vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint
  apply T.vacuumOrthogonalClosedRightHamiltonian_isSelfAdjoint_of_dense
  simpa only [vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint] using
    T.vacuumOrthogonalClosedRightHamiltonian_dense_domain hP hSelf

/-- The excitation-sector Hamiltonian is graph closed. -/
theorem vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint_isClosed
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) :
    LinearPMap.IsClosed
      (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf) :=
  (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint_isSelfAdjoint
    hP hSelf).isClosed

/-- Complete excitation-sector operator package. -/
theorem vacuumOrthogonalClosedRightHamiltonian_operator_package
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) :
    Dense (((T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf).domain :
      Set P.VacuumOrthogonalHilbert)) ∧
      IsSelfAdjoint
        (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf) ∧
      LinearPMap.IsClosed
        (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf) :=
  ⟨T.vacuumOrthogonalClosedRightHamiltonian_dense_domain hP hSelf,
    T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint_isSelfAdjoint hP hSelf,
    T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint_isClosed hP hSelf⟩

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end MathlibAnalytic
end MGAP4D

end
