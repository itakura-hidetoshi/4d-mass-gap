import MGAP4D.MathlibAnalytic.FiniteProductParallelVariationContraction
import MGAP4D.MathlibAnalytic.FinitePositiveWeightHilbertRealization
import MGAP4D.MathlibAnalytic.SymmetricEigenvalueUpperBound

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A parallel finite-product operator equipped simultaneously with a strict
variation-matrix contraction, weighted reversibility, and preservation of the
constant observable.  These are exactly the generic inputs needed to turn a
direct parallel coupling estimate into a centered weighted Rayleigh bound. -/
structure FinitePositiveWeightParallelReversibleData
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (T : ((ι → G) → ℝ) →ₗ[ℝ] ((ι → G) → ℝ)) where
  variationData : FiniteProductParallelVariationMatrixData T
  pairing_symm :
    ∀ f g : (ι → G) → ℝ,
      finitePositiveWeightPairing weight (T f) g =
        finitePositiveWeightPairing weight f (T g)
  constant_fixed :
    T (fun _ : ι → G => (1 : ℝ)) =
      (fun _ : ι → G => (1 : ℝ))

/-- Transport an arbitrary observable-space linear operator through the
positive-weight square-root realization. -/
noncomputable def finitePositiveWeightHilbertTransportLinearMap
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (T : ((ι → G) → ℝ) →ₗ[ℝ] ((ι → G) → ℝ)) :
    FinitePositiveWeightHilbertSpace ι G →ₗ[ℝ]
      FinitePositiveWeightHilbertSpace ι G :=
  (finitePositiveWeightHilbertEmbedLinearMap weight).comp
    (T.comp (finitePositiveWeightHilbertObserveLinearMap weight))

@[simp] theorem finitePositiveWeightHilbertTransportLinearMap_apply
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (T : ((ι → G) → ℝ) →ₗ[ℝ] ((ι → G) → ℝ))
    (x : FinitePositiveWeightHilbertSpace ι G) :
    finitePositiveWeightHilbertTransportLinearMap weight T x =
      finitePositiveWeightHilbertEmbedLinearMap weight
        (T (finitePositiveWeightHilbertObserveLinearMap weight x)) := by
  rfl

/-- The transported operator intertwines with positive-weight embedding. -/
theorem finitePositiveWeightHilbertTransportLinearMap_embed
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (T : ((ι → G) → ℝ) →ₗ[ℝ] ((ι → G) → ℝ))
    (f : (ι → G) → ℝ) :
    finitePositiveWeightHilbertTransportLinearMap weight T
        (finitePositiveWeightHilbertEmbedLinearMap weight f) =
      finitePositiveWeightHilbertEmbedLinearMap weight (T f) := by
  rw [finitePositiveWeightHilbertTransportLinearMap_apply,
    finitePositiveWeightHilbert_observe_embed weight hweight f]

/-- Weighted reversibility is ordinary Hilbert symmetry after square-root
transport. -/
theorem finitePositiveWeightHilbertTransportLinearMap_isSymmetric
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (T : ((ι → G) → ℝ) →ₗ[ℝ] ((ι → G) → ℝ))
    (D : FinitePositiveWeightParallelReversibleData weight T) :
    (finitePositiveWeightHilbertTransportLinearMap weight T).IsSymmetric := by
  intro x y
  calc
    inner ℝ (finitePositiveWeightHilbertTransportLinearMap weight T x) y =
      inner ℝ
        (finitePositiveWeightHilbertTransportLinearMap weight T
          (finitePositiveWeightHilbertEmbedLinearMap weight
            (finitePositiveWeightHilbertObserveLinearMap weight x)))
        (finitePositiveWeightHilbertEmbedLinearMap weight
          (finitePositiveWeightHilbertObserveLinearMap weight y)) := by
      rw [finitePositiveWeightHilbert_embed_observe weight hweight x,
        finitePositiveWeightHilbert_embed_observe weight hweight y]
    _ = inner ℝ
        (finitePositiveWeightHilbertEmbedLinearMap weight
          (T (finitePositiveWeightHilbertObserveLinearMap weight x)))
        (finitePositiveWeightHilbertEmbedLinearMap weight
          (finitePositiveWeightHilbertObserveLinearMap weight y)) := by
      rw [finitePositiveWeightHilbertTransportLinearMap_embed
        weight hweight T]
    _ = finitePositiveWeightPairing weight
        (T (finitePositiveWeightHilbertObserveLinearMap weight x))
        (finitePositiveWeightHilbertObserveLinearMap weight y) :=
      finitePositiveWeightHilbert_inner_embed weight hweight _ _
    _ = finitePositiveWeightPairing weight
        (finitePositiveWeightHilbertObserveLinearMap weight x)
        (T (finitePositiveWeightHilbertObserveLinearMap weight y)) :=
      D.pairing_symm _ _
    _ = inner ℝ
        (finitePositiveWeightHilbertEmbedLinearMap weight
          (finitePositiveWeightHilbertObserveLinearMap weight x))
        (finitePositiveWeightHilbertEmbedLinearMap weight
          (T (finitePositiveWeightHilbertObserveLinearMap weight y))) :=
      (finitePositiveWeightHilbert_inner_embed weight hweight _ _).symm
    _ = inner ℝ
        (finitePositiveWeightHilbertEmbedLinearMap weight
          (finitePositiveWeightHilbertObserveLinearMap weight x))
        (finitePositiveWeightHilbertTransportLinearMap weight T
          (finitePositiveWeightHilbertEmbedLinearMap weight
            (finitePositiveWeightHilbertObserveLinearMap weight y))) := by
      rw [finitePositiveWeightHilbertTransportLinearMap_embed
        weight hweight T]
    _ = inner ℝ x
        (finitePositiveWeightHilbertTransportLinearMap weight T y) := by
      rw [finitePositiveWeightHilbert_embed_observe weight hweight x,
        finitePositiveWeightHilbert_embed_observe weight hweight y]

/-- Constant preservation becomes vacuum preservation after transport. -/
theorem finitePositiveWeightHilbertTransportLinearMap_vacuum
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (T : ((ι → G) → ℝ) →ₗ[ℝ] ((ι → G) → ℝ))
    (D : FinitePositiveWeightParallelReversibleData weight T) :
    finitePositiveWeightHilbertTransportLinearMap weight T
        (finitePositiveWeightHilbertVacuum weight) =
      finitePositiveWeightHilbertVacuum weight := by
  rw [finitePositiveWeightHilbertVacuum,
    finitePositiveWeightHilbertTransportLinearMap_embed weight hweight T,
    D.constant_fixed]

/-- A reversible constant-preserving parallel operator preserves the weighted
centered Hilbert sector. -/
theorem finitePositiveWeightHilbertTransport_preserves_vacuumOrthogonal
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (T : ((ι → G) → ℝ) →ₗ[ℝ] ((ι → G) → ℝ))
    (D : FinitePositiveWeightParallelReversibleData weight T)
    (x : FinitePositiveWeightHilbertSpace ι G)
    (hx : x ∈ finiteVacuumOrthogonal
      (finitePositiveWeightHilbertVacuum weight)) :
    finitePositiveWeightHilbertTransportLinearMap weight T x ∈
      finiteVacuumOrthogonal (finitePositiveWeightHilbertVacuum weight) := by
  rw [finite_wilson_mem_vacuumOrthogonal_iff]
  have hOrth :
      inner ℝ (finitePositiveWeightHilbertVacuum weight) x = 0 :=
    (finite_wilson_mem_vacuumOrthogonal_iff
      (finitePositiveWeightHilbertVacuum weight) x).mp hx
  calc
    inner ℝ (finitePositiveWeightHilbertVacuum weight)
        (finitePositiveWeightHilbertTransportLinearMap weight T x) =
      inner ℝ (finitePositiveWeightHilbertTransportLinearMap weight T x)
        (finitePositiveWeightHilbertVacuum weight) := real_inner_comm _ _
    _ = inner ℝ x
        (finitePositiveWeightHilbertTransportLinearMap weight T
          (finitePositiveWeightHilbertVacuum weight)) :=
      finitePositiveWeightHilbertTransportLinearMap_isSymmetric
        weight hweight T D x (finitePositiveWeightHilbertVacuum weight)
    _ = inner ℝ x (finitePositiveWeightHilbertVacuum weight) := by
      rw [finitePositiveWeightHilbertTransportLinearMap_vacuum
        weight hweight T D]
    _ = inner ℝ (finitePositiveWeightHilbertVacuum weight) x :=
      real_inner_comm _ _
    _ = 0 := hOrth

/-- Restriction of a parallel reversible operator to the weighted-centered
Hilbert sector. -/
noncomputable def finitePositiveWeightHilbertTransportRestrictedLinearMap
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (T : ((ι → G) → ℝ) →ₗ[ℝ] ((ι → G) → ℝ))
    (D : FinitePositiveWeightParallelReversibleData weight T) :
    finiteVacuumOrthogonal (finitePositiveWeightHilbertVacuum weight) →ₗ[ℝ]
      finiteVacuumOrthogonal (finitePositiveWeightHilbertVacuum weight) :=
  (finitePositiveWeightHilbertTransportLinearMap weight T).restrict
    (finitePositiveWeightHilbertTransport_preserves_vacuumOrthogonal
      weight hweight T D)

/-- The weighted-centered restriction is symmetric. -/
theorem finitePositiveWeightHilbertTransportRestrictedLinearMap_isSymmetric
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (T : ((ι → G) → ℝ) →ₗ[ℝ] ((ι → G) → ℝ))
    (D : FinitePositiveWeightParallelReversibleData weight T) :
    (finitePositiveWeightHilbertTransportRestrictedLinearMap
      weight hweight T D).IsSymmetric :=
  (finitePositiveWeightHilbertTransportLinearMap_isSymmetric
    weight hweight T D).restrict_invariant
      (finitePositiveWeightHilbertTransport_preserves_vacuumOrthogonal
        weight hweight T D)

/-- Every nonzero centered Hilbert eigenvector inherits the direct parallel
variation coefficient bound. -/
theorem finitePositiveWeightHilbertTransportRestricted_eigenvalue_abs_le
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (T : ((ι → G) → ℝ) →ₗ[ℝ] ((ι → G) → ℝ))
    (D : FinitePositiveWeightParallelReversibleData weight T)
    (x : finiteVacuumOrthogonal (finitePositiveWeightHilbertVacuum weight))
    (r : ℝ)
    (hx : x ≠ 0)
    (hEigen : finitePositiveWeightHilbertTransportRestrictedLinearMap
      weight hweight T D x = r • x) :
    |r| ≤ D.variationData.coefficient := by
  let f : (ι → G) → ℝ :=
    finitePositiveWeightHilbertObserveLinearMap weight
      (x : FinitePositiveWeightHilbertSpace ι G)
  have hOrth :
      inner ℝ (finitePositiveWeightHilbertVacuum weight)
        (x : FinitePositiveWeightHilbertSpace ι G) = 0 :=
    (finite_wilson_mem_vacuumOrthogonal_iff
      (finitePositiveWeightHilbertVacuum weight)
      (x : FinitePositiveWeightHilbertSpace ι G)).mp x.property
  have hCenter : finitePositiveWeightSum weight f = 0 := by
    rw [← finitePositiveWeightHilbert_inner_vacuum_embed
      weight hweight f,
      finitePositiveWeightHilbert_embed_observe weight hweight
        (x : FinitePositiveWeightHilbertSpace ι G)]
    exact hOrth
  have hf : f ≠ 0 := by
    intro hf
    apply hx
    apply Subtype.ext
    change (x : FinitePositiveWeightHilbertSpace ι G) = 0
    calc
      (x : FinitePositiveWeightHilbertSpace ι G) =
          finitePositiveWeightHilbertEmbedLinearMap weight f :=
        (finitePositiveWeightHilbert_embed_observe weight hweight
          (x : FinitePositiveWeightHilbertSpace ι G)).symm
      _ = 0 := by simp [hf]
  have hEigenHilbert :
      finitePositiveWeightHilbertTransportLinearMap weight T
          (x : FinitePositiveWeightHilbertSpace ι G) =
        r • (x : FinitePositiveWeightHilbertSpace ι G) := by
    simpa [finitePositiveWeightHilbertTransportRestrictedLinearMap]
      using congrArg
        (fun y : finiteVacuumOrthogonal
            (finitePositiveWeightHilbertVacuum weight) =>
          (y : FinitePositiveWeightHilbertSpace ι G)) hEigen
  have hEmbeddedEigen :
      finitePositiveWeightHilbertEmbedLinearMap weight (T f) =
        r • finitePositiveWeightHilbertEmbedLinearMap weight f := by
    rw [← finitePositiveWeightHilbertTransportLinearMap_embed
      weight hweight T f,
      finitePositiveWeightHilbert_embed_observe weight hweight
        (x : FinitePositiveWeightHilbertSpace ι G)]
    exact hEigenHilbert
  have hObservableEigen : T f = r • f := by
    calc
      T f = finitePositiveWeightHilbertObserveLinearMap weight
          (finitePositiveWeightHilbertEmbedLinearMap weight (T f)) :=
        (finitePositiveWeightHilbert_observe_embed weight hweight (T f)).symm
      _ = finitePositiveWeightHilbertObserveLinearMap weight
          (r • finitePositiveWeightHilbertEmbedLinearMap weight f) :=
        congrArg
          (fun y : FinitePositiveWeightHilbertSpace ι G =>
            finitePositiveWeightHilbertObserveLinearMap weight y)
          hEmbeddedEigen
      _ = r • f := by
        rw [map_smul,
          finitePositiveWeightHilbert_observe_embed weight hweight]
  exact finitePositiveWeight_centered_parallel_eigenvalue_abs_le_coefficient
    weight hweight T D.variationData f r hCenter hf hObservableEigen

/-- Direct parallel variation contraction lifts through the finite-dimensional
symmetric eigenbasis to a centered weighted Hilbert Rayleigh bound. -/
theorem finitePositiveWeightHilbertTransportRestricted_rayleigh_le
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (T : ((ι → G) → ℝ) →ₗ[ℝ] ((ι → G) → ℝ))
    (D : FinitePositiveWeightParallelReversibleData weight T)
    (x : finiteVacuumOrthogonal (finitePositiveWeightHilbertVacuum weight)) :
    inner ℝ
        (finitePositiveWeightHilbertTransportRestrictedLinearMap
          weight hweight T D x) x ≤
      D.variationData.coefficient * ‖x‖ ^ 2 := by
  let hT := finitePositiveWeightHilbertTransportRestrictedLinearMap_isSymmetric
    weight hweight T D
  apply symmetric_quadraticForm_le_of_eigenvalues_le
    hT rfl D.variationData.coefficient ?_ x
  intro i
  have hAbs :=
    finitePositiveWeightHilbertTransportRestricted_eigenvalue_abs_le
      weight hweight T D
      (hT.eigenvectorBasis rfl i)
      (hT.eigenvalues rfl i)
      ((hT.eigenvectorBasis rfl).toBasis.ne_zero i)
      (hT.apply_eigenvectorBasis rfl i)
  exact le_trans (le_abs_self _) hAbs

/-- Observable-space centered weighted Rayleigh contraction for a reversible
constant-preserving parallel operator with strict variation coefficient. -/
theorem finitePositiveWeight_centered_parallel_rayleigh_le
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (T : ((ι → G) → ℝ) →ₗ[ℝ] ((ι → G) → ℝ))
    (D : FinitePositiveWeightParallelReversibleData weight T)
    (f : (ι → G) → ℝ)
    (hCenter : finitePositiveWeightSum weight f = 0) :
    finitePositiveWeightPairing weight (T f) f ≤
      D.variationData.coefficient *
        finitePositiveWeightPairing weight f f := by
  have hx :
      finitePositiveWeightHilbertEmbedLinearMap weight f ∈
        finiteVacuumOrthogonal (finitePositiveWeightHilbertVacuum weight) := by
    rw [finite_wilson_mem_vacuumOrthogonal_iff,
      finitePositiveWeightHilbert_inner_vacuum_embed weight hweight]
    exact hCenter
  let x : finiteVacuumOrthogonal
      (finitePositiveWeightHilbertVacuum weight) :=
    ⟨finitePositiveWeightHilbertEmbedLinearMap weight f, hx⟩
  have hRayleigh :=
    finitePositiveWeightHilbertTransportRestricted_rayleigh_le
      weight hweight T D x
  change
    inner ℝ
        (finitePositiveWeightHilbertTransportLinearMap weight T
          (finitePositiveWeightHilbertEmbedLinearMap weight f))
        (finitePositiveWeightHilbertEmbedLinearMap weight f) ≤
      D.variationData.coefficient *
        ‖finitePositiveWeightHilbertEmbedLinearMap weight f‖ ^ 2 at hRayleigh
  rw [finitePositiveWeightHilbertTransportLinearMap_embed weight hweight T,
    finitePositiveWeightHilbert_inner_embed weight hweight,
    finitePositiveWeightHilbert_norm_sq_embed weight hweight] at hRayleigh
  exact hRayleigh

end

end MathlibAnalytic
end MGAP4D
