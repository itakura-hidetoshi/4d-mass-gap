import MGAP4D.MathlibAnalytic.FiniteDimensionalGroundNullOperatorCharacterization
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProduct

noncomputable section

namespace FiniteDimensionalSymmetricPositiveContractionData

variable
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (D : FiniteDimensionalSymmetricPositiveContractionData E)

/-- The complete canonical spectral-coordinate Hilbert space. -/
abbrev FullSpectralSpace : Type :=
  EuclideanSpace ℝ (Fin D.dimension)

/-- Restrict complete canonical coordinates to the ground sector. -/
noncomputable def fullGroundCoordinates :
    D.FullSpectralSpace →ₗ[ℝ] D.GroundSpectralSpace where
  toFun := fun x => WithLp.toLp 2 (fun i => x i.1)
  map_add' := by
    intro x y
    ext i
    simp
  map_smul' := by
    intro c x
    ext i
    simp

/-- Restrict complete canonical coordinates to the strictly excited sector. -/
noncomputable def fullExcitedCoordinates :
    D.FullSpectralSpace →ₗ[ℝ] D.ExcitedSpectralSpace where
  toFun := fun x => WithLp.toLp 2 (fun i => x i.1)
  map_add' := by
    intro x y
    ext i
    simp
  map_smul' := by
    intro c x
    ext i
    simp

/-- Restrict complete canonical coordinates to the null sector. -/
noncomputable def fullNullCoordinates :
    D.FullSpectralSpace →ₗ[ℝ] D.NullSpectralSpace where
  toFun := fun x => WithLp.toLp 2 (fun i => x i.1)
  map_add' := by
    intro x y
    ext i
    simp
  map_smul' := by
    intro c x
    ext i
    simp

@[simp] theorem fullGroundCoordinates_groundSpectralExtension
    (x : D.GroundSpectralSpace) :
    D.fullGroundCoordinates (D.groundSpectralExtension x) = x := by
  ext i
  simp [fullGroundCoordinates, groundSpectralExtension, i.2]

@[simp] theorem fullExcitedCoordinates_excitedSpectralExtension
    (x : D.ExcitedSpectralSpace) :
    D.fullExcitedCoordinates (D.excitedSpectralExtension x) = x := by
  ext i
  simp [fullExcitedCoordinates, excitedSpectralExtension, i.2]

@[simp] theorem fullNullCoordinates_nullSpectralExtension
    (x : D.NullSpectralSpace) :
    D.fullNullCoordinates (D.nullSpectralExtension x) = x := by
  ext i
  simp [fullNullCoordinates, nullSpectralExtension, i.2]

@[simp] theorem fullGroundCoordinates_excitedSpectralExtension
    (x : D.ExcitedSpectralSpace) :
    D.fullGroundCoordinates (D.excitedSpectralExtension x) = 0 := by
  ext i
  have hne := D.ground_not_excited i.1 i.2
  simp [fullGroundCoordinates, excitedSpectralExtension, hne]

@[simp] theorem fullGroundCoordinates_nullSpectralExtension
    (x : D.NullSpectralSpace) :
    D.fullGroundCoordinates (D.nullSpectralExtension x) = 0 := by
  ext i
  have hne := D.ground_not_null i.1 i.2
  simp [fullGroundCoordinates, nullSpectralExtension, hne]

@[simp] theorem fullExcitedCoordinates_groundSpectralExtension
    (x : D.GroundSpectralSpace) :
    D.fullExcitedCoordinates (D.groundSpectralExtension x) = 0 := by
  ext i
  have hne := D.ground_not_excited i.1 i.2
  simp [fullExcitedCoordinates, groundSpectralExtension, hne]

@[simp] theorem fullExcitedCoordinates_nullSpectralExtension
    (x : D.NullSpectralSpace) :
    D.fullExcitedCoordinates (D.nullSpectralExtension x) = 0 := by
  ext i
  have hne := D.excited_not_null i.1 i.2
  simp [fullExcitedCoordinates, nullSpectralExtension, hne]

@[simp] theorem fullNullCoordinates_groundSpectralExtension
    (x : D.GroundSpectralSpace) :
    D.fullNullCoordinates (D.groundSpectralExtension x) = 0 := by
  ext i
  have hne := D.ground_not_null i.1 i.2
  simp [fullNullCoordinates, groundSpectralExtension, hne]

@[simp] theorem fullNullCoordinates_excitedSpectralExtension
    (x : D.ExcitedSpectralSpace) :
    D.fullNullCoordinates (D.excitedSpectralExtension x) = 0 := by
  ext i
  have hne := D.excited_not_null i.1 i.2
  simp [fullNullCoordinates, excitedSpectralExtension, hne]

/-- Every complete canonical coordinate vector is exactly the sum of its
three mutually disjoint spectral sectors. -/
theorem fullSpectral_ground_add_excited_add_null
    (x : D.FullSpectralSpace) :
    D.groundSpectralExtension (D.fullGroundCoordinates x) +
        D.excitedSpectralExtension (D.fullExcitedCoordinates x) +
        D.nullSpectralExtension (D.fullNullCoordinates x) = x := by
  ext i
  rcases D.eigenvalue_trichotomy i with hz | he | hg
  · have hng : D.eigenvalue i ≠ 1 := by
      rw [hz]
      norm_num
    have hne : ¬(0 < D.eigenvalue i ∧ D.eigenvalue i < 1) := by
      rw [hz]
      norm_num
    simp [groundSpectralExtension, excitedSpectralExtension,
      nullSpectralExtension, fullGroundCoordinates,
      fullExcitedCoordinates, fullNullCoordinates, hz, hng, hne]
  · have hnz : D.eigenvalue i ≠ 0 := D.excited_not_null i he
    have hng : D.eigenvalue i ≠ 1 := ne_of_lt he.2
    simp [groundSpectralExtension, excitedSpectralExtension,
      nullSpectralExtension, fullGroundCoordinates,
      fullExcitedCoordinates, fullNullCoordinates, he, hnz, hng]
  · have hnz : D.eigenvalue i ≠ 0 := D.ground_not_null i hg
    have hne : ¬(0 < D.eigenvalue i ∧ D.eigenvalue i < 1) :=
      D.ground_not_excited i hg
    simp [groundSpectralExtension, excitedSpectralExtension,
      nullSpectralExtension, fullGroundCoordinates,
      fullExcitedCoordinates, fullNullCoordinates, hg, hnz, hne]

/-- Ground and excited coordinate sectors are orthogonal in the complete
canonical spectral Hilbert space. -/
theorem groundSpectralExtension_orthogonal_excitedSpectralExtension
    (x : D.GroundSpectralSpace)
    (y : D.ExcitedSpectralSpace) :
    inner ℝ (D.groundSpectralExtension x)
      (D.excitedSpectralExtension y) = 0 := by
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro i _hi
  by_cases hg : D.eigenvalue i = 1
  · have hne := D.ground_not_excited i hg
    simp [groundSpectralExtension, excitedSpectralExtension, hg, hne]
  · simp [groundSpectralExtension, hg]

/-- Ground and null coordinate sectors are orthogonal in the complete
canonical spectral Hilbert space. -/
theorem groundSpectralExtension_orthogonal_nullSpectralExtension
    (x : D.GroundSpectralSpace)
    (z : D.NullSpectralSpace) :
    inner ℝ (D.groundSpectralExtension x)
      (D.nullSpectralExtension z) = 0 := by
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro i _hi
  by_cases hg : D.eigenvalue i = 1
  · have hnz := D.ground_not_null i hg
    simp [groundSpectralExtension, nullSpectralExtension, hg, hnz]
  · simp [groundSpectralExtension, hg]

/-- Excited and null coordinate sectors are orthogonal in the complete
canonical spectral Hilbert space. -/
theorem excitedSpectralExtension_orthogonal_nullSpectralExtension
    (y : D.ExcitedSpectralSpace)
    (z : D.NullSpectralSpace) :
    inner ℝ (D.excitedSpectralExtension y)
      (D.nullSpectralExtension z) = 0 := by
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro i _hi
  by_cases he : 0 < D.eigenvalue i ∧ D.eigenvalue i < 1
  · have hnz := D.excited_not_null i he
    simp [excitedSpectralExtension, nullSpectralExtension, he, hnz]
  · simp [excitedSpectralExtension, he]

/-- Ground coordinates of a vector in the original Hilbert space. -/
noncomputable def groundCoordinates : E →ₗ[ℝ] D.GroundSpectralSpace :=
  D.fullGroundCoordinates.comp D.eigenbasis.repr.toLinearMap

/-- Strictly excited coordinates of a vector in the original Hilbert space. -/
noncomputable def excitedCoordinates : E →ₗ[ℝ] D.ExcitedSpectralSpace :=
  D.fullExcitedCoordinates.comp D.eigenbasis.repr.toLinearMap

/-- Null coordinates of a vector in the original Hilbert space. -/
noncomputable def nullCoordinates : E →ₗ[ℝ] D.NullSpectralSpace :=
  D.fullNullCoordinates.comp D.eigenbasis.repr.toLinearMap

@[simp] theorem groundCoordinates_groundSpectralSynthesis
    (x : D.GroundSpectralSpace) :
    D.groundCoordinates (D.groundSpectralSynthesis x) = x := by
  simpa [groundCoordinates, groundSpectralSynthesis] using
    D.fullGroundCoordinates_groundSpectralExtension x

@[simp] theorem excitedCoordinates_excitedSpectralSynthesis
    (x : D.ExcitedSpectralSpace) :
    D.excitedCoordinates (D.excitedSpectralSynthesis x) = x := by
  simpa [excitedCoordinates, excitedSpectralSynthesis] using
    D.fullExcitedCoordinates_excitedSpectralExtension x

@[simp] theorem nullCoordinates_nullSpectralSynthesis
    (x : D.NullSpectralSpace) :
    D.nullCoordinates (D.nullSpectralSynthesis x) = x := by
  simpa [nullCoordinates, nullSpectralSynthesis] using
    D.fullNullCoordinates_nullSpectralExtension x

@[simp] theorem groundCoordinates_excitedSpectralSynthesis
    (x : D.ExcitedSpectralSpace) :
    D.groundCoordinates (D.excitedSpectralSynthesis x) = 0 := by
  simpa [groundCoordinates, excitedSpectralSynthesis] using
    D.fullGroundCoordinates_excitedSpectralExtension x

@[simp] theorem groundCoordinates_nullSpectralSynthesis
    (x : D.NullSpectralSpace) :
    D.groundCoordinates (D.nullSpectralSynthesis x) = 0 := by
  simpa [groundCoordinates, nullSpectralSynthesis] using
    D.fullGroundCoordinates_nullSpectralExtension x

@[simp] theorem excitedCoordinates_groundSpectralSynthesis
    (x : D.GroundSpectralSpace) :
    D.excitedCoordinates (D.groundSpectralSynthesis x) = 0 := by
  simpa [excitedCoordinates, groundSpectralSynthesis] using
    D.fullExcitedCoordinates_groundSpectralExtension x

@[simp] theorem excitedCoordinates_nullSpectralSynthesis
    (x : D.NullSpectralSpace) :
    D.excitedCoordinates (D.nullSpectralSynthesis x) = 0 := by
  simpa [excitedCoordinates, nullSpectralSynthesis] using
    D.fullExcitedCoordinates_nullSpectralExtension x

@[simp] theorem nullCoordinates_groundSpectralSynthesis
    (x : D.GroundSpectralSpace) :
    D.nullCoordinates (D.groundSpectralSynthesis x) = 0 := by
  simpa [nullCoordinates, groundSpectralSynthesis] using
    D.fullNullCoordinates_groundSpectralExtension x

@[simp] theorem nullCoordinates_excitedSpectralSynthesis
    (x : D.ExcitedSpectralSpace) :
    D.nullCoordinates (D.excitedSpectralSynthesis x) = 0 := by
  simpa [nullCoordinates, excitedSpectralSynthesis] using
    D.fullNullCoordinates_excitedSpectralExtension x

/-- Exact reconstruction of every original Hilbert-space vector from ground,
strictly excited, and null synthesis. -/
theorem groundSynthesis_add_excitedSynthesis_add_nullSynthesis
    (x : E) :
    D.groundSpectralSynthesis (D.groundCoordinates x) +
        D.excitedSpectralSynthesis (D.excitedCoordinates x) +
        D.nullSpectralSynthesis (D.nullCoordinates x) = x := by
  apply D.eigenbasis.repr.injective
  simpa [groundCoordinates, excitedCoordinates, nullCoordinates,
    groundSpectralSynthesis, excitedSpectralSynthesis,
    nullSpectralSynthesis] using
    D.fullSpectral_ground_add_excited_add_null (D.eigenbasis.repr x)

/-- Diagonal transfer on the strictly excited sector. -/
noncomputable def excitedSpectralTransfer :
    D.ExcitedSpectralSpace →L[ℝ] D.ExcitedSpectralSpace :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (fun i => D.eigenvalue i.1 * x i)
      map_add' := by
        intro x y
        ext i
        simp [mul_add]
      map_smul' := by
        intro c x
        ext i
        change D.eigenvalue i.1 * (c * x i) =
          c * (D.eigenvalue i.1 * x i)
        ring }

@[simp] theorem excitedSpectralTransfer_apply
    (x : D.ExcitedSpectralSpace)
    (i : D.ExcitedSpectralIndex) :
    D.excitedSpectralTransfer x i = D.eigenvalue i.1 * x i := by
  rfl

/-- Modewise inverse of the strictly excited transfer. -/
noncomputable def excitedSpectralInverse :
    D.ExcitedSpectralSpace →L[ℝ] D.ExcitedSpectralSpace :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (fun i => x i / D.eigenvalue i.1)
      map_add' := by
        intro x y
        ext i
        simp [add_div]
      map_smul' := by
        intro c x
        ext i
        change (c * x i) / D.eigenvalue i.1 =
          c * (x i / D.eigenvalue i.1)
        ring }

@[simp] theorem excitedSpectralInverse_apply
    (x : D.ExcitedSpectralSpace)
    (i : D.ExcitedSpectralIndex) :
    D.excitedSpectralInverse x i = x i / D.eigenvalue i.1 := by
  rfl

@[simp] theorem excitedSpectralTransfer_excitedSpectralInverse
    (x : D.ExcitedSpectralSpace) :
    D.excitedSpectralTransfer (D.excitedSpectralInverse x) = x := by
  ext i
  change D.eigenvalue i.1 * (x i / D.eigenvalue i.1) = x i
  field_simp [ne_of_gt i.2.1]

@[simp] theorem excitedSpectralInverse_excitedSpectralTransfer
    (x : D.ExcitedSpectralSpace) :
    D.excitedSpectralInverse (D.excitedSpectralTransfer x) = x := by
  ext i
  change (D.eigenvalue i.1 * x i) / D.eigenvalue i.1 = x i
  field_simp [ne_of_gt i.2.1]

/-- The strictly excited transfer is injective. -/
theorem excitedSpectralTransfer_injective :
    Function.Injective D.excitedSpectralTransfer := by
  intro x y hxy
  have := congrArg D.excitedSpectralInverse hxy
  simpa using this

/-- The original operator intertwines excited synthesis with the diagonal
strictly excited transfer. -/
theorem operator_excitedSpectralSynthesis
    (x : D.ExcitedSpectralSpace) :
    D.operator (D.excitedSpectralSynthesis x) =
      D.excitedSpectralSynthesis (D.excitedSpectralTransfer x) := by
  apply D.eigenbasis.repr.injective
  ext j
  have hdiag :
      D.eigenbasis.repr
          (D.operator (D.excitedSpectralSynthesis x)) j =
        D.eigenvalue j *
          D.eigenbasis.repr (D.excitedSpectralSynthesis x) j := by
    simpa [eigenbasis, eigenvalue] using
      D.symmetric.eigenvectorBasis_apply_self_apply
        (by rfl) (D.excitedSpectralSynthesis x) j
  rw [hdiag]
  by_cases he : 0 < D.eigenvalue j ∧ D.eigenvalue j < 1
  · simp [excitedSpectralSynthesis, excitedSpectralExtension,
      excitedSpectralTransfer, he]
  · simp [excitedSpectralSynthesis, excitedSpectralExtension,
      excitedSpectralTransfer, he]

/-- Ground coordinates are preserved by one transfer step. -/
theorem groundCoordinates_operator (x : E) :
    D.groundCoordinates (D.operator x) = D.groundCoordinates x := by
  ext i
  have hdiag :
      D.eigenbasis.repr (D.operator x) i.1 =
        D.eigenvalue i.1 * D.eigenbasis.repr x i.1 := by
    simpa [eigenbasis, eigenvalue] using
      D.symmetric.eigenvectorBasis_apply_self_apply (by rfl) x i.1
  simpa [groundCoordinates, fullGroundCoordinates, i.2] using hdiag

/-- Excited coordinates evolve by the diagonal strictly excited transfer. -/
theorem excitedCoordinates_operator (x : E) :
    D.excitedCoordinates (D.operator x) =
      D.excitedSpectralTransfer (D.excitedCoordinates x) := by
  ext i
  have hdiag :
      D.eigenbasis.repr (D.operator x) i.1 =
        D.eigenvalue i.1 * D.eigenbasis.repr x i.1 := by
    simpa [eigenbasis, eigenvalue] using
      D.symmetric.eigenvectorBasis_apply_self_apply (by rfl) x i.1
  simpa [excitedCoordinates, fullExcitedCoordinates,
    excitedSpectralTransfer] using hdiag

/-- Null coordinates vanish after one transfer step. -/
theorem nullCoordinates_operator (x : E) :
    D.nullCoordinates (D.operator x) = 0 := by
  ext i
  have hdiag :
      D.eigenbasis.repr (D.operator x) i.1 =
        D.eigenvalue i.1 * D.eigenbasis.repr x i.1 := by
    simpa [eigenbasis, eigenvalue] using
      D.symmetric.eigenvectorBasis_apply_self_apply (by rfl) x i.1
  simpa [nullCoordinates, fullNullCoordinates, i.2] using hdiag

/-- The complete one-step operator decomposition: ground is fixed, excited
coordinates evolve modewise, and null coordinates disappear. -/
theorem operator_eq_ground_add_excited
    (x : E) :
    D.operator x =
      D.groundSpectralSynthesis (D.groundCoordinates x) +
        D.excitedSpectralSynthesis
          (D.excitedSpectralTransfer (D.excitedCoordinates x)) := by
  rw [← D.groundSynthesis_add_excitedSynthesis_add_nullSynthesis x]
  simp [map_add, D.operator_groundSpectralSynthesis,
    D.operator_excitedSpectralSynthesis,
    D.operator_nullSpectralSynthesis]

/-- The operator kernel is exactly the synthesized null sector. -/
theorem operator_eq_zero_iff_eq_nullSynthesis
    (x : E) :
    D.operator x = 0 ↔
      x = D.nullSpectralSynthesis (D.nullCoordinates x) := by
  constructor
  · intro hx
    have hg := D.groundCoordinates_operator x
    rw [hx] at hg
    have hg0 : D.groundCoordinates x = 0 := by
      simpa using hg.symm
    have he := D.excitedCoordinates_operator x
    rw [hx] at he
    have hte : D.excitedSpectralTransfer (D.excitedCoordinates x) = 0 := by
      simpa using he.symm
    have he0 : D.excitedCoordinates x = 0 :=
      D.excitedSpectralTransfer_injective
        (show D.excitedSpectralTransfer (D.excitedCoordinates x) =
            D.excitedSpectralTransfer 0 by simpa using hte)
    calc
      x = D.groundSpectralSynthesis (D.groundCoordinates x) +
          D.excitedSpectralSynthesis (D.excitedCoordinates x) +
          D.nullSpectralSynthesis (D.nullCoordinates x) :=
        (D.groundSynthesis_add_excitedSynthesis_add_nullSynthesis x).symm
      _ = D.nullSpectralSynthesis (D.nullCoordinates x) := by
        simp [hg0, he0]
  · intro hx
    rw [hx]
    exact D.operator_nullSpectralSynthesis (D.nullCoordinates x)

/-- A strictly excited vector cannot be fixed except at zero. -/
theorem excitedSpectralTransfer_eq_self_iff
    (x : D.ExcitedSpectralSpace) :
    D.excitedSpectralTransfer x = x ↔ x = 0 := by
  constructor
  · intro hx
    ext i
    have hi := congrArg (fun y : D.ExcitedSpectralSpace => y i) hx
    change D.eigenvalue i.1 * x i = x i at hi
    have : x i = 0 := by
      nlinarith [i.2.2]
    simpa using this
  · intro hx
    simp [hx]

/-- The fixed-point space is exactly the synthesized ground sector. -/
theorem operator_eq_self_iff_eq_groundSynthesis
    (x : E) :
    D.operator x = x ↔
      x = D.groundSpectralSynthesis (D.groundCoordinates x) := by
  constructor
  · intro hx
    have he := D.excitedCoordinates_operator x
    rw [hx] at he
    have he0 : D.excitedCoordinates x = 0 :=
      (D.excitedSpectralTransfer_eq_self_iff
        (D.excitedCoordinates x)).mp he
    have hn := D.nullCoordinates_operator x
    rw [hx] at hn
    have hn0 : D.nullCoordinates x = 0 := by
      simpa using hn
    calc
      x = D.groundSpectralSynthesis (D.groundCoordinates x) +
          D.excitedSpectralSynthesis (D.excitedCoordinates x) +
          D.nullSpectralSynthesis (D.nullCoordinates x) :=
        (D.groundSynthesis_add_excitedSynthesis_add_nullSynthesis x).symm
      _ = D.groundSpectralSynthesis (D.groundCoordinates x) := by
        simp [he0, hn0]
  · intro hx
    rw [hx]
    exact D.operator_groundSpectralSynthesis (D.groundCoordinates x)

/-- A vector lies in the range of the operator exactly when its null
coordinates vanish. -/
theorem exists_operator_preimage_iff_nullCoordinates_eq_zero
    (y : E) :
    (∃ x : E, D.operator x = y) ↔ D.nullCoordinates y = 0 := by
  constructor
  · rintro ⟨x, rfl⟩
    exact D.nullCoordinates_operator x
  · intro hy
    refine ⟨
      D.groundSpectralSynthesis (D.groundCoordinates y) +
        D.excitedSpectralSynthesis
          (D.excitedSpectralInverse (D.excitedCoordinates y)), ?_⟩
    calc
      D.operator
          (D.groundSpectralSynthesis (D.groundCoordinates y) +
            D.excitedSpectralSynthesis
              (D.excitedSpectralInverse (D.excitedCoordinates y))) =
          D.groundSpectralSynthesis (D.groundCoordinates y) +
            D.excitedSpectralSynthesis (D.excitedCoordinates y) := by
        simp [map_add, D.operator_groundSpectralSynthesis,
          D.operator_excitedSpectralSynthesis]
      _ = y := by
        have hrec :=
          D.groundSynthesis_add_excitedSynthesis_add_nullSynthesis y
        rw [hy] at hrec
        simpa using hrec

end FiniteDimensionalSymmetricPositiveContractionData

end

end MathlibAnalytic
end MGAP4D
