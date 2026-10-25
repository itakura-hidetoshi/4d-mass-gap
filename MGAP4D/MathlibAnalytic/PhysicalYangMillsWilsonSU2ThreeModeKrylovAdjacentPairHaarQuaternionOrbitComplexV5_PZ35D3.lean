import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarQuaternionTraceDualityV5_PZ35D2
import Mathlib.Tactic

/-!
# P4-Q2-PZ35D3 — genuine SU(2) quaternion orbit, exact COMPLEX trace sum

D2 proved the universal complex Pauli trace dual pairing by a transport
of the unconditional PZ35A matrix decomposition. Here four genuine
quaternion elements of the SAME original SU(2) group are proved to have
the corresponding inverse matrices. Algebraic trace cyclicity and the
group inverse law then give an unconditional, pointwise four-orbit
complex trace identity:
  sum_j Tr(q_j u) Tr((q_j u)^(-1) b) = 2 Tr(b).

This remains a finite-dimensional exact identity INSIDE genuine SU(2),
not integration over the finite quaternion subgroup. The full
continuous-group Haar part was already formalized in PZ35C.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Mat" => Matrix (Fin 2) (Fin 2) ℂ
local notation "q" => p4Q2PZ35B_quaternionFamily

/-- Four fixed matrices used in PZ35A and now realized by PZ35B in SU(2). -/
def p4Q2PZ35D3_pauliMatrix : Fin 4 → Mat :=
  ![p4Q2PZ35A_pauliQ0, p4Q2PZ35A_pauliQ1,
    p4Q2PZ35A_pauliQ2, p4Q2PZ35A_pauliQ3]

/-- Their literal inverse matrices, with signs determined by SU(2)
unitarity and the quaternion square relations. -/
def p4Q2PZ35D3_pauliInverse : Fin 4 → Mat :=
  ![p4Q2PZ35A_pauliQ0, -p4Q2PZ35A_pauliQ1,
    -p4Q2PZ35A_pauliQ2, -p4Q2PZ35A_pauliQ3]

/-- Every PZ35B genuine SU(2) quaternion inverse has exactly
the expected 2x2 complex matrix representative. -/
theorem p4Q2PZ35D3_quaternionInverse_coe (j : Fin 4) :
    (((q j)⁻¹ : G) : Mat) = p4Q2PZ35D3_pauliInverse j := by
  have hStar :
      (((q j)⁻¹ : G) : Mat) =
        ((q j : G) : Mat).conjTranspose := by
    calc
      (((q j)⁻¹ : G) : Mat) =
          ((star (q j) : G) : Mat) := by
            rw [Matrix.star_eq_inv]
      _ = star ((q j : G) : Mat) :=
        Matrix.specialUnitaryGroup.coe_star (q j)
      _ = ((q j : G) : Mat).conjTranspose := rfl
  rw [hStar, p4Q2PZ35B_quaternionFamily_coe j]
  fin_cases j <;>
    (ext i k
     fin_cases i <;> fin_cases k <;>
       simp [p4Q2PZ35D3_pauliInverse,
         p4Q2PZ35A_pauliQ0, p4Q2PZ35A_pauliQ1,
         p4Q2PZ35A_pauliQ2, p4Q2PZ35A_pauliQ3,
         Matrix.conjTranspose_apply])

/-- Actual Fin 4 trace bilinear sum from the PZ35A/D2 matrix
decomposition; NO assumption on either complex 2x2 matrix. -/
theorem p4Q2PZ35D3_complexTracePair_sum (A C : Mat) :
    (∑ j : Fin 4,
      Matrix.trace (p4Q2PZ35D3_pauliMatrix j * A) *
        Matrix.trace (C * p4Q2PZ35D3_pauliInverse j)) =
      2 * Matrix.trace (C * A) := by
  simpa [Fin.sum_univ_four,
    p4Q2PZ35D3_pauliMatrix, p4Q2PZ35D3_pauliInverse,
    mul_neg, sub_eq_add_neg, add_assoc] using
      (p4Q2PZ35D2_complexPauliTracePair A C)

/-- Unconditional quaternion orbit sum in the complex trace of
actual SU(2) group products. In particular no Schur orthogonality
hypothesis is inserted. -/
theorem p4Q2PZ35D3_SU2_complexOrbitTrace (b u : G) :
    (∑ j : Fin 4,
      Matrix.trace (((q j * u : G) : Mat)) *
        Matrix.trace ((((q j * u)⁻¹ * b : G) : Mat))) =
      2 * Matrix.trace (b : Mat) := by
  have hTerm (j : Fin 4) :
      Matrix.trace (((q j * u : G) : Mat)) *
          Matrix.trace ((((q j * u)⁻¹ * b : G) : Mat)) =
        Matrix.trace (p4Q2PZ35D3_pauliMatrix j * (u : Mat)) *
          Matrix.trace ((((b * u⁻¹ : G) : Mat)) *
            p4Q2PZ35D3_pauliInverse j) := by
    have hGroup : (q j * u)⁻¹ * b = u⁻¹ * (q j)⁻¹ * b := by
      group
    rw [hGroup]
    change
      Matrix.trace (((q j : G) : Mat) * (u : Mat)) *
          Matrix.trace ((((u⁻¹ : G) : Mat) *
            (((q j)⁻¹ : G) : Mat)) * (b : Mat)) =
        Matrix.trace (p4Q2PZ35D3_pauliMatrix j * (u : Mat)) *
          Matrix.trace (((b : Mat) * ((u⁻¹ : G) : Mat)) *
            p4Q2PZ35D3_pauliInverse j)
    rw [Matrix.trace_mul_cycle]
    rw [p4Q2PZ35B_quaternionFamily_coe j,
      p4Q2PZ35D3_quaternionInverse_coe j]
    rfl
  calc
    (∑ j : Fin 4,
        Matrix.trace (((q j * u : G) : Mat)) *
          Matrix.trace ((((q j * u)⁻¹ * b : G) : Mat))) =
      ∑ j : Fin 4,
        Matrix.trace (p4Q2PZ35D3_pauliMatrix j * (u : Mat)) *
          Matrix.trace (((b * u⁻¹ : G) : Mat) *
            p4Q2PZ35D3_pauliInverse j) := by
      apply Finset.sum_congr rfl
      intro j _hj
      exact hTerm j
    _ = 2 * Matrix.trace (((b * u⁻¹ : G) : Mat) * (u : Mat)) :=
      p4Q2PZ35D3_complexTracePair_sum (u : Mat) ((b * u⁻¹ : G) : Mat)
    _ = 2 * Matrix.trace (b : Mat) := by
      change 2 * Matrix.trace (((b * u⁻¹ * u : G) : Mat)) =
        2 * Matrix.trace (b : Mat)
      simp [mul_assoc]

end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ35D3_quaternionInverse_coe
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ35D3_complexTracePair_sum
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ35D3_SU2_complexOrbitTrace
