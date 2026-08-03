import MGAP4D.MathlibAnalytic.FiniteDimensionalFullGroundExcitationNullDecomposition
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace FiniteDimensionalSymmetricPositiveContractionData

variable
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (D : FiniteDimensionalSymmetricPositiveContractionData E)

/-- Natural-time powers of the diagonal transfer on the strictly excited
sector. -/
noncomputable def excitedSpectralSemigroup (n : ℕ) :
    D.ExcitedSpectralSpace →L[ℝ] D.ExcitedSpectralSpace :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x =>
        WithLp.toLp 2 (fun i => (D.eigenvalue i.1) ^ n * x i)
      map_add' := by
        intro x y
        ext i
        simp [mul_add]
      map_smul' := by
        intro c x
        ext i
        change (D.eigenvalue i.1) ^ n * (c * x i) =
          c * ((D.eigenvalue i.1) ^ n * x i)
        ring }

@[simp] theorem excitedSpectralSemigroup_apply
    (n : ℕ)
    (x : D.ExcitedSpectralSpace)
    (i : D.ExcitedSpectralIndex) :
    D.excitedSpectralSemigroup n x i =
      (D.eigenvalue i.1) ^ n * x i := by
  rfl

/-- Zero natural time is the identity on the excited coordinate space. -/
theorem excitedSpectralSemigroup_zero :
    D.excitedSpectralSemigroup 0 = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  ext i
  simp

/-- One natural-time step is the diagonal excited transfer. -/
theorem excitedSpectralSemigroup_one :
    D.excitedSpectralSemigroup 1 = D.excitedSpectralTransfer := by
  apply ContinuousLinearMap.ext
  intro x
  ext i
  simp

/-- Excited natural time is additive under composition. -/
theorem excitedSpectralSemigroup_add (m n : ℕ) :
    D.excitedSpectralSemigroup (m + n) =
      (D.excitedSpectralSemigroup m).comp
        (D.excitedSpectralSemigroup n) := by
  apply ContinuousLinearMap.ext
  intro x
  ext i
  simp [pow_add, mul_assoc]

/-- Complete natural-time evolution reconstructed from the three spectral
sectors.  Ground coordinates persist, excited coordinates evolve by their
diagonal powers, and null coordinates are retained only at time zero. -/
noncomputable def fullSpectralNaturalTime (n : ℕ) : E →L[ℝ] E :=
  LinearMap.toContinuousLinearMap
    (D.groundSpectralSynthesis.comp D.groundCoordinates +
      D.excitedSpectralSynthesis.comp
        ((D.excitedSpectralSemigroup n).toLinearMap.comp
          D.excitedCoordinates) +
      if n = 0 then
        D.nullSpectralSynthesis.comp D.nullCoordinates
      else 0)

/-- Ground coordinates are invariant at every natural time. -/
theorem groundCoordinates_fullSpectralNaturalTime
    (n : ℕ)
    (x : E) :
    D.groundCoordinates (D.fullSpectralNaturalTime n x) =
      D.groundCoordinates x := by
  by_cases hn : n = 0
  · subst n
    simp [fullSpectralNaturalTime]
  · simp [fullSpectralNaturalTime, hn]

/-- Excited coordinates evolve by the exact diagonal natural-time semigroup. -/
theorem excitedCoordinates_fullSpectralNaturalTime
    (n : ℕ)
    (x : E) :
    D.excitedCoordinates (D.fullSpectralNaturalTime n x) =
      D.excitedSpectralSemigroup n (D.excitedCoordinates x) := by
  by_cases hn : n = 0
  · subst n
    simp [fullSpectralNaturalTime]
  · simp [fullSpectralNaturalTime, hn]

/-- Null coordinates are present only at natural time zero. -/
theorem nullCoordinates_fullSpectralNaturalTime
    (n : ℕ)
    (x : E) :
    D.nullCoordinates (D.fullSpectralNaturalTime n x) =
      if n = 0 then D.nullCoordinates x else 0 := by
  by_cases hn : n = 0
  · subst n
    simp [fullSpectralNaturalTime]
  · simp [fullSpectralNaturalTime, hn]

/-- At natural time zero the complete evolution is the identity. -/
theorem fullSpectralNaturalTime_zero :
    D.fullSpectralNaturalTime 0 = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  simpa [fullSpectralNaturalTime, excitedSpectralSemigroup] using
    D.groundSynthesis_add_excitedSynthesis_add_nullSynthesis x

/-- At one natural-time step the complete evolution is the original
operator. -/
theorem fullSpectralNaturalTime_one :
    D.fullSpectralNaturalTime 1 = D.operator := by
  apply ContinuousLinearMap.ext
  intro x
  simpa [fullSpectralNaturalTime, excitedSpectralSemigroup,
    excitedSpectralTransfer] using
    (D.operator_eq_ground_add_excited x).symm

/-- Complete natural time is additive under composition. -/
theorem fullSpectralNaturalTime_add (m n : ℕ) :
    D.fullSpectralNaturalTime (m + n) =
      (D.fullSpectralNaturalTime m).comp
        (D.fullSpectralNaturalTime n) := by
  apply ContinuousLinearMap.ext
  intro x
  by_cases hm : m = 0
  · subst m
    simp [D.fullSpectralNaturalTime_zero]
  by_cases hn : n = 0
  · subst n
    simp [D.fullSpectralNaturalTime_zero]
  have hmn : m + n ≠ 0 := Nat.add_ne_zero.mpr ⟨hm, hn⟩
  simp [fullSpectralNaturalTime, hm, hn, hmn,
    D.groundCoordinates_fullSpectralNaturalTime,
    D.excitedCoordinates_fullSpectralNaturalTime,
    D.excitedSpectralSemigroup_add]

/-- Positive natural time has no null component. -/
theorem nullCoordinates_fullSpectralNaturalTime_eq_zero
    (n : ℕ)
    (hn : 0 < n)
    (x : E) :
    D.nullCoordinates (D.fullSpectralNaturalTime n x) = 0 := by
  rw [D.nullCoordinates_fullSpectralNaturalTime]
  simp [Nat.ne_of_gt hn]

/-- At every positive natural time the state is exactly ground plus evolved
excited synthesis; the null sector has disappeared. -/
theorem fullSpectralNaturalTime_eq_ground_add_excited
    (n : ℕ)
    (hn : 0 < n)
    (x : E) :
    D.fullSpectralNaturalTime n x =
      D.groundSpectralSynthesis (D.groundCoordinates x) +
        D.excitedSpectralSynthesis
          (D.excitedSpectralSemigroup n (D.excitedCoordinates x)) := by
  simp [fullSpectralNaturalTime, Nat.ne_of_gt hn]

/-- The complete natural-time semigroup obeys the expected one-step
recursion. -/
theorem fullSpectralNaturalTime_succ (n : ℕ) :
    D.fullSpectralNaturalTime (n + 1) =
      D.operator.comp (D.fullSpectralNaturalTime n) := by
  calc
    D.fullSpectralNaturalTime (n + 1) =
        (D.fullSpectralNaturalTime 1).comp
          (D.fullSpectralNaturalTime n) := by
      simpa [Nat.add_comm] using D.fullSpectralNaturalTime_add 1 n
    _ = D.operator.comp (D.fullSpectralNaturalTime n) := by
      rw [D.fullSpectralNaturalTime_one]

end FiniteDimensionalSymmetricPositiveContractionData

end

end MathlibAnalytic
end MGAP4D
