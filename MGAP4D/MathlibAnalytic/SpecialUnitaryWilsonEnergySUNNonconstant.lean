import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonKernelFeatureNorm
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyPowerHaarModes
import Mathlib.Tactic

/-!
# Explicit nonconstant Wilson energy on SU(N), N >= 2

The previous SU(2) lane used an explicit rotation subgroup to prove that the
Wilson plaquette energy is nonconstant.  For the arbitrary-rank route we only
need a much smaller fact.

For every N >= 2, put -1 in two diagonal slots and 1 in all remaining slots.
This matrix is unitary, has determinant one, and therefore defines an element
of SU(N).  Its normalized real trace differs from the identity, so the Wilson
plaquette energy is genuinely nonconstant for every N >= 2.

This explicit witness is the finite-dimensional input needed to construct
rank-uniform Haar modes without falling back to the SU(2)-specific
Gram--Schmidt family.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Matrix MeasureTheory
open scoped BigOperators

noncomputable section

/-- The first diagonal index used by the rank-uniform SU(N) witness. -/
def specialUnitaryTwoNegativeIndexZero
    (N : ℕ) (hN : 2 ≤ N) : Fin N :=
  ⟨0, lt_of_lt_of_le (by norm_num) hN⟩

/-- The second diagonal index used by the rank-uniform SU(N) witness. -/
def specialUnitaryTwoNegativeIndexOne
    (N : ℕ) (hN : 2 ≤ N) : Fin N :=
  ⟨1, hN⟩

theorem specialUnitaryTwoNegativeIndexZero_ne_one
    (N : ℕ) (hN : 2 ≤ N) :
    specialUnitaryTwoNegativeIndexZero N hN ≠
      specialUnitaryTwoNegativeIndexOne N hN := by
  intro h
  have := congrArg Fin.val h
  norm_num [specialUnitaryTwoNegativeIndexZero,
    specialUnitaryTwoNegativeIndexOne] at this

/-- Diagonal entries of the explicit arbitrary-rank SU(N) witness. -/
def specialUnitaryTwoNegativeDiagonalEntry
    (N : ℕ) (hN : 2 ≤ N) : Fin N → ℂ :=
  Function.update
    (Function.update
      (fun _ : Fin N => (1 : ℂ))
      (specialUnitaryTwoNegativeIndexZero N hN)
      (-1 : ℂ))
    (specialUnitaryTwoNegativeIndexOne N hN)
    (-1 : ℂ)

/-- The corresponding diagonal complex matrix. -/
def specialUnitaryTwoNegativeDiagonalMatrix
    (N : ℕ) (hN : 2 ≤ N) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal (specialUnitaryTwoNegativeDiagonalEntry N hN)

/-- The two-negative diagonal witness is unitary. -/
theorem specialUnitaryTwoNegativeDiagonalMatrix_mem_unitaryGroup
    (N : ℕ) (hN : 2 ≤ N) :
    specialUnitaryTwoNegativeDiagonalMatrix N hN ∈
      Matrix.unitaryGroup (Fin N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi1 :
        i = specialUnitaryTwoNegativeIndexOne N hN
    · subst i
      simp [specialUnitaryTwoNegativeDiagonalMatrix,
        specialUnitaryTwoNegativeDiagonalEntry,
        Matrix.star_eq_conjTranspose]
    · by_cases hi0 :
          i = specialUnitaryTwoNegativeIndexZero N hN
      · subst i
        simp [specialUnitaryTwoNegativeDiagonalMatrix,
          specialUnitaryTwoNegativeDiagonalEntry,
          Matrix.star_eq_conjTranspose,
          specialUnitaryTwoNegativeIndexZero_ne_one N hN]
      · simp [specialUnitaryTwoNegativeDiagonalMatrix,
          specialUnitaryTwoNegativeDiagonalEntry,
          Matrix.star_eq_conjTranspose, hi0, hi1]
  · simp [specialUnitaryTwoNegativeDiagonalMatrix,
      specialUnitaryTwoNegativeDiagonalEntry,
      Matrix.star_eq_conjTranspose, hij]

/-- The two-negative diagonal witness has determinant one. -/
theorem specialUnitaryTwoNegativeDiagonalMatrix_det
    (N : ℕ) (hN : 2 ≤ N) :
    Matrix.det (specialUnitaryTwoNegativeDiagonalMatrix N hN) = 1 := by
  classical
  rw [specialUnitaryTwoNegativeDiagonalMatrix, Matrix.det_diagonal]
  simp [specialUnitaryTwoNegativeDiagonalEntry,
    Finset.prod_update_of_mem,
    specialUnitaryTwoNegativeIndexZero_ne_one N hN]

/-- The explicit arbitrary-rank witness packaged as an element of SU(N). -/
def specialUnitaryTwoNegativeDiagonal
    (N : ℕ) (hN : 2 ≤ N) :
    Matrix.specialUnitaryGroup (Fin N) ℂ :=
  ⟨specialUnitaryTwoNegativeDiagonalMatrix N hN,
    specialUnitaryTwoNegativeDiagonalMatrix_mem_unitaryGroup N hN,
    specialUnitaryTwoNegativeDiagonalMatrix_det N hN⟩

/-- Its trace is N - 4, viewed in C. -/
theorem specialUnitaryTwoNegativeDiagonal_trace
    (N : ℕ) (hN : 2 ≤ N) :
    Matrix.trace
        ((specialUnitaryTwoNegativeDiagonal N hN :
          Matrix.specialUnitaryGroup (Fin N) ℂ) :
          Matrix (Fin N) (Fin N) ℂ) =
      (N : ℂ) - 4 := by
  classical
  change
    Matrix.trace (specialUnitaryTwoNegativeDiagonalMatrix N hN) =
      (N : ℂ) - 4
  rw [specialUnitaryTwoNegativeDiagonalMatrix, Matrix.trace_diagonal]
  let i0 := specialUnitaryTwoNegativeIndexZero N hN
  let i1 := specialUnitaryTwoNegativeIndexOne N hN
  have h01 : i0 ≠ i1 := by
    simpa [i0, i1] using
      specialUnitaryTwoNegativeIndexZero_ne_one N hN
  have hcard :
      (((Finset.univ : Finset (Fin N)) \ {i1}) \ {i0}).card =
        N - 2 := by
    rw [Finset.card_sdiff_of_subset]
    · rw [Finset.card_sdiff_of_subset]
      · simp
      · simp
    · simp [h01]
  simp [specialUnitaryTwoNegativeDiagonalEntry,
    Finset.sum_update_of_mem,
    specialUnitaryTwoNegativeIndexZero_ne_one N hN]
  rw [hcard, Nat.cast_sub hN]
  norm_num
  ring

/-- The normalized real trace of the witness is 1 - 4/N. -/
theorem normalizedSpecialUnitaryRealTrace_twoNegativeDiagonal
    (N : ℕ) (hN : 2 ≤ N) :
    normalizedSpecialUnitaryRealTrace N
        (specialUnitaryTwoNegativeDiagonal N hN) =
      1 - 4 / (N : ℝ) := by
  rw [normalizedSpecialUnitaryRealTrace_eq_trace_re_div,
    specialUnitaryTwoNegativeDiagonal_trace]
  have hN0 : (N : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) hN))
  norm_num
  field_simp [hN0]

/-- The Wilson plaquette energy of the witness is exactly 4/N. -/
theorem specialUnitaryWilsonPlaquetteEnergy_twoNegativeDiagonal
    (N : ℕ) (hN : 2 ≤ N) :
    specialUnitaryWilsonPlaquetteEnergy N
        (specialUnitaryTwoNegativeDiagonal N hN) =
      4 / (N : ℝ) := by
  rw [specialUnitaryWilsonPlaquetteEnergy_eq,
    normalizedSpecialUnitaryRealTrace_twoNegativeDiagonal N hN]
  ring

/-- The explicit witness has strictly positive Wilson plaquette energy. -/
theorem specialUnitaryWilsonPlaquetteEnergy_twoNegativeDiagonal_pos
    (N : ℕ) (hN : 2 ≤ N) :
    0 <
      specialUnitaryWilsonPlaquetteEnergy N
        (specialUnitaryTwoNegativeDiagonal N hN) := by
  rw [specialUnitaryWilsonPlaquetteEnergy_twoNegativeDiagonal N hN]
  positivity

/-- Therefore the Wilson plaquette energy on SU(N) is nonconstant for every
rank N >= 2. -/
theorem specialUnitaryWilsonPlaquetteEnergy_not_constant
    (N : ℕ) (hN : 2 ≤ N) :
    ¬ ∃ c : ℝ, ∀ U : Matrix.specialUnitaryGroup (Fin N) ℂ,
      specialUnitaryWilsonPlaquetteEnergy N U = c := by
  rintro ⟨c, hc⟩
  have hOne := hc (1 : Matrix.specialUnitaryGroup (Fin N) ℂ)
  have hWitness := hc (specialUnitaryTwoNegativeDiagonal N hN)
  rw [specialUnitaryWilsonPlaquetteEnergy_one N
      (lt_of_lt_of_le (by norm_num) hN)] at hOne
  have hPos :=
    specialUnitaryWilsonPlaquetteEnergy_twoNegativeDiagonal_pos N hN
  rw [hWitness, ← hOne] at hPos
  exact (lt_irrefl 0) hPos

/-- In particular, the constant-one function and Wilson-energy function are
pointwise distinct on SU(N). -/
theorem specialUnitaryWilsonPlaquetteEnergy_ne_const_zero
    (N : ℕ) (hN : 2 ≤ N) :
    (specialUnitaryWilsonPlaquetteEnergy N) ≠
      (fun _ : Matrix.specialUnitaryGroup (Fin N) ℂ => (0 : ℝ)) := by
  intro h
  have hw := congrFun h (specialUnitaryTwoNegativeDiagonal N hN)
  have hPos :=
    specialUnitaryWilsonPlaquetteEnergy_twoNegativeDiagonal_pos N hN
  simp at hw
  linarith

end

end MathlibAnalytic
end MGAP4D
