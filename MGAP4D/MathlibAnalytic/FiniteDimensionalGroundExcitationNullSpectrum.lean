import MGAP4D.MathlibAnalytic.FiniteDimensionalPositiveSpectralSupportHamiltonian
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

/-- Transfer eigenmodes with eigenvalue exactly one.  These are the zero-energy
modes of the positive-support Hamiltonian. -/
def GroundSpectralIndex : Type :=
  {i : Fin D.dimension // D.eigenvalue i = 1}

/-- Strictly positive transfer modes below the norm-one level. -/
def ExcitedSpectralIndex : Type :=
  {i : Fin D.dimension // 0 < D.eigenvalue i ∧ D.eigenvalue i < 1}

/-- Transfer modes annihilated in one natural-time step. -/
def NullSpectralIndex : Type :=
  {i : Fin D.dimension // D.eigenvalue i = 0}

noncomputable instance groundSpectralIndexFintype :
    Fintype D.GroundSpectralIndex := by
  classical
  unfold GroundSpectralIndex
  infer_instance

noncomputable instance excitedSpectralIndexFintype :
    Fintype D.ExcitedSpectralIndex := by
  classical
  unfold ExcitedSpectralIndex
  infer_instance

noncomputable instance nullSpectralIndexFintype :
    Fintype D.NullSpectralIndex := by
  classical
  unfold NullSpectralIndex
  infer_instance

noncomputable instance groundSpectralIndexDecidableEq :
    DecidableEq D.GroundSpectralIndex :=
  Classical.decEq _

noncomputable instance excitedSpectralIndexDecidableEq :
    DecidableEq D.ExcitedSpectralIndex :=
  Classical.decEq _

noncomputable instance nullSpectralIndexDecidableEq :
    DecidableEq D.NullSpectralIndex :=
  Classical.decEq _

/-- Euclidean Hilbert space of norm-one transfer modes. -/
abbrev GroundSpectralSpace : Type :=
  EuclideanSpace ℝ D.GroundSpectralIndex

/-- Euclidean Hilbert space of strictly decaying positive transfer modes. -/
abbrev ExcitedSpectralSpace : Type :=
  EuclideanSpace ℝ D.ExcitedSpectralIndex

/-- Euclidean Hilbert space of transfer zero modes. -/
abbrev NullSpectralSpace : Type :=
  EuclideanSpace ℝ D.NullSpectralIndex

/-- Every eigenmode of a positive contraction is null, strictly excited, or
ground. -/
theorem eigenvalue_trichotomy (i : Fin D.dimension) :
    D.eigenvalue i = 0 ∨
      (0 < D.eigenvalue i ∧ D.eigenvalue i < 1) ∨
      D.eigenvalue i = 1 := by
  rcases D.eigenvalue_mem_unitInterval i with ⟨h0, h1⟩
  by_cases hz : D.eigenvalue i = 0
  · exact Or.inl hz
  by_cases hg : D.eigenvalue i = 1
  · exact Or.inr (Or.inr hg)
  exact Or.inr (Or.inl ⟨lt_of_le_of_ne h0 (Ne.symm hz), lt_of_le_of_ne h1 hg⟩)

/-- Ground and excited indices are disjoint. -/
theorem ground_not_excited
    (i : Fin D.dimension)
    (hg : D.eigenvalue i = 1) :
    ¬(0 < D.eigenvalue i ∧ D.eigenvalue i < 1) := by
  intro he
  rw [hg] at he
  exact (lt_irrefl 1) he.2

/-- Ground and null indices are disjoint. -/
theorem ground_not_null
    (i : Fin D.dimension)
    (hg : D.eigenvalue i = 1) :
    D.eigenvalue i ≠ 0 := by
  rw [hg]
  norm_num

/-- Excited and null indices are disjoint. -/
theorem excited_not_null
    (i : Fin D.dimension)
    (he : 0 < D.eigenvalue i ∧ D.eigenvalue i < 1) :
    D.eigenvalue i ≠ 0 :=
  ne_of_gt he.1

/-- A ground index is canonically a positive-support index. -/
def GroundSpectralIndex.toPositive
    (i : D.GroundSpectralIndex) : D.PositiveSpectralIndex :=
  ⟨i.1, by rw [i.2]; norm_num⟩

/-- An excited index is canonically a positive-support index. -/
def ExcitedSpectralIndex.toPositive
    (i : D.ExcitedSpectralIndex) : D.PositiveSpectralIndex :=
  ⟨i.1, i.2.1⟩

/-- Zero extension of ground coordinates to all canonical transfer modes. -/
noncomputable def groundSpectralExtension :
    D.GroundSpectralSpace →ₗ[ℝ]
      EuclideanSpace ℝ (Fin D.dimension) where
  toFun := fun x =>
    WithLp.toLp 2 (fun j =>
      if h : D.eigenvalue j = 1 then x ⟨j, h⟩ else 0)
  map_add' := by
    intro x y
    ext j
    by_cases h : D.eigenvalue j = 1 <;> simp [h]
  map_smul' := by
    intro c x
    ext j
    by_cases h : D.eigenvalue j = 1 <;> simp [h]

/-- Zero extension of excited coordinates to all canonical transfer modes. -/
noncomputable def excitedSpectralExtension :
    D.ExcitedSpectralSpace →ₗ[ℝ]
      EuclideanSpace ℝ (Fin D.dimension) where
  toFun := fun x =>
    WithLp.toLp 2 (fun j =>
      if h : 0 < D.eigenvalue j ∧ D.eigenvalue j < 1 then x ⟨j, h⟩ else 0)
  map_add' := by
    intro x y
    ext j
    by_cases h : 0 < D.eigenvalue j ∧ D.eigenvalue j < 1 <;> simp [h]
  map_smul' := by
    intro c x
    ext j
    by_cases h : 0 < D.eigenvalue j ∧ D.eigenvalue j < 1 <;> simp [h]

/-- Zero extension of null coordinates to all canonical transfer modes. -/
noncomputable def nullSpectralExtension :
    D.NullSpectralSpace →ₗ[ℝ]
      EuclideanSpace ℝ (Fin D.dimension) where
  toFun := fun x =>
    WithLp.toLp 2 (fun j =>
      if h : D.eigenvalue j = 0 then x ⟨j, h⟩ else 0)
  map_add' := by
    intro x y
    ext j
    by_cases h : D.eigenvalue j = 0 <;> simp [h]
  map_smul' := by
    intro c x
    ext j
    by_cases h : D.eigenvalue j = 0 <;> simp [h]

@[simp] theorem groundSpectralExtension_apply
    (x : D.GroundSpectralSpace)
    (i : D.GroundSpectralIndex) :
    D.groundSpectralExtension x i.1 = x i := by
  simp [groundSpectralExtension, i.2]

@[simp] theorem excitedSpectralExtension_apply
    (x : D.ExcitedSpectralSpace)
    (i : D.ExcitedSpectralIndex) :
    D.excitedSpectralExtension x i.1 = x i := by
  simp [excitedSpectralExtension, i.2]

@[simp] theorem nullSpectralExtension_apply
    (x : D.NullSpectralSpace)
    (i : D.NullSpectralIndex) :
    D.nullSpectralExtension x i.1 = x i := by
  simp [nullSpectralExtension, i.2]

/-- Synthesis of ground coordinates in the original Hilbert space. -/
noncomputable def groundSpectralSynthesis :
    D.GroundSpectralSpace →ₗ[ℝ] E :=
  D.eigenbasis.repr.symm.toLinearMap.comp D.groundSpectralExtension

/-- Synthesis of excited coordinates in the original Hilbert space. -/
noncomputable def excitedSpectralSynthesis :
    D.ExcitedSpectralSpace →ₗ[ℝ] E :=
  D.eigenbasis.repr.symm.toLinearMap.comp D.excitedSpectralExtension

/-- Synthesis of null coordinates in the original Hilbert space. -/
noncomputable def nullSpectralSynthesis :
    D.NullSpectralSpace →ₗ[ℝ] E :=
  D.eigenbasis.repr.symm.toLinearMap.comp D.nullSpectralExtension

/-- Ground synthesis is injective. -/
theorem groundSpectralSynthesis_injective :
    Function.Injective D.groundSpectralSynthesis := by
  intro x y hxy
  ext i
  have hcoord := congrArg (fun z : E => D.eigenbasis.repr z i.1) hxy
  simpa [groundSpectralSynthesis, i.2] using hcoord

/-- Excited synthesis is injective. -/
theorem excitedSpectralSynthesis_injective :
    Function.Injective D.excitedSpectralSynthesis := by
  intro x y hxy
  ext i
  have hcoord := congrArg (fun z : E => D.eigenbasis.repr z i.1) hxy
  simpa [excitedSpectralSynthesis, i.2] using hcoord

/-- Null synthesis is injective. -/
theorem nullSpectralSynthesis_injective :
    Function.Injective D.nullSpectralSynthesis := by
  intro x y hxy
  ext i
  have hcoord := congrArg (fun z : E => D.eigenbasis.repr z i.1) hxy
  simpa [nullSpectralSynthesis, i.2] using hcoord

end FiniteDimensionalSymmetricPositiveContractionData

end

end MathlibAnalytic
end MGAP4D
