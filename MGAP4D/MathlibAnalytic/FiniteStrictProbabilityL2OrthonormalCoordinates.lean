import MGAP4D.MathlibAnalytic.RealHilbertLinearIsometricOperatorTransport
import MGAP4D.MathlibAnalytic.OrthonormalDiagonalOperator
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators InnerProduct

noncomputable section

/-- Strictly positive probability weights on a finite index type. -/
structure FiniteStrictProbabilityL2Data
    (ι : Type)
    [Fintype ι] where
  weight : ι → ℝ
  weight_pos : ∀ i : ι, 0 < weight i
  weight_sum : ∑ i : ι, weight i = 1

/-- Square-root-density coordinate carrier of a finite probability `L²`
space.  The underlying finite-dimensional Hilbert space depends only on the
index type; the probability weights determine how observables are embedded. -/
abbrev FiniteProbabilityL2Carrier
    (ι : Type)
    [Fintype ι] : Type :=
  EuclideanSpace ℝ ι

namespace FiniteStrictProbabilityL2Data

variable
    {ι : Type}
    [Fintype ι]
    (P : FiniteStrictProbabilityL2Data ι)

/-- Send an observable `f` to the Euclidean coordinate
`sqrt(weight i) * f i`. -/
noncomputable def observableEmbedLinearMap :
    (ι → ℝ) →ₗ[ℝ] FiniteProbabilityL2Carrier ι where
  toFun f :=
    WithLp.toLp 2 fun i : ι => Real.sqrt (P.weight i) * f i
  map_add' f g := by
    ext i
    change Real.sqrt (P.weight i) * (f i + g i) =
      Real.sqrt (P.weight i) * f i +
        Real.sqrt (P.weight i) * g i
    ring
  map_smul' c f := by
    ext i
    change Real.sqrt (P.weight i) * (c * f i) =
      c * (Real.sqrt (P.weight i) * f i)
    ring

@[simp] theorem observableEmbedLinearMap_apply
    (f : ι → ℝ)
    (i : ι) :
    P.observableEmbedLinearMap f i =
      Real.sqrt (P.weight i) * f i :=
  rfl

/-- Recover the observable represented by square-root-density coordinates. -/
noncomputable def coordinateObserveLinearMap :
    FiniteProbabilityL2Carrier ι →ₗ[ℝ] (ι → ℝ) where
  toFun x := fun i : ι => x i / Real.sqrt (P.weight i)
  map_add' x y := by
    funext i
    change (x i + y i) / Real.sqrt (P.weight i) =
      x i / Real.sqrt (P.weight i) +
        y i / Real.sqrt (P.weight i)
    ring
  map_smul' c x := by
    funext i
    change (c * x i) / Real.sqrt (P.weight i) =
      c * (x i / Real.sqrt (P.weight i))
    ring

@[simp] theorem coordinateObserveLinearMap_apply
    (x : FiniteProbabilityL2Carrier ι)
    (i : ι) :
    P.coordinateObserveLinearMap x i =
      x i / Real.sqrt (P.weight i) :=
  rfl

/-- Every square-root probability density is nonzero. -/
theorem sqrt_weight_ne_zero
    (i : ι) :
    Real.sqrt (P.weight i) ≠ 0 :=
  ne_of_gt (Real.sqrt_pos.2 (P.weight_pos i))

/-- Observing an embedded finite-probability observable recovers it exactly. -/
theorem coordinateObserve_observableEmbed
    (f : ι → ℝ) :
    P.coordinateObserveLinearMap
        (P.observableEmbedLinearMap f) = f := by
  funext i
  rw [P.coordinateObserveLinearMap_apply,
    P.observableEmbedLinearMap_apply]
  field_simp [P.sqrt_weight_ne_zero i]

/-- Embedding the recovered observable returns the original coordinate vector. -/
theorem observableEmbed_coordinateObserve
    (x : FiniteProbabilityL2Carrier ι) :
    P.observableEmbedLinearMap
        (P.coordinateObserveLinearMap x) = x := by
  ext i
  rw [P.observableEmbedLinearMap_apply,
    P.coordinateObserveLinearMap_apply]
  field_simp [P.sqrt_weight_ne_zero i]

/-- The Euclidean inner product of square-root-density coordinates is exactly
the finite probability `L²` pairing. -/
theorem inner_observableEmbed
    (f g : ι → ℝ) :
    inner ℝ (P.observableEmbedLinearMap f)
        (P.observableEmbedLinearMap g) =
      ∑ i : ι, P.weight i * f i * g i := by
  classical
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  change
    (Real.sqrt (P.weight i) * g i) *
        (Real.sqrt (P.weight i) * f i) =
      P.weight i * f i * g i
  calc
    (Real.sqrt (P.weight i) * g i) *
        (Real.sqrt (P.weight i) * f i) =
      (Real.sqrt (P.weight i)) ^ 2 * f i * g i := by
        ring
    _ = P.weight i * f i * g i := by
      rw [Real.sq_sqrt (le_of_lt (P.weight_pos i))]

/-- The coordinate norm is the weighted finite-probability `L²` norm. -/
theorem norm_sq_observableEmbed
    (f : ι → ℝ) :
    ‖P.observableEmbedLinearMap f‖ ^ 2 =
      ∑ i : ι, P.weight i * f i ^ 2 := by
  calc
    ‖P.observableEmbedLinearMap f‖ ^ 2 =
        inner ℝ (P.observableEmbedLinearMap f)
          (P.observableEmbedLinearMap f) := by
      simpa using
        (real_inner_self_eq_norm_sq
          (P.observableEmbedLinearMap f)).symm
    _ = ∑ i : ι, P.weight i * f i * f i :=
      P.inner_observableEmbed f f
    _ = ∑ i : ι, P.weight i * f i ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _hi
      ring

end FiniteStrictProbabilityL2Data

/-- Uniform probability weights on a finite nonempty type. -/
noncomputable def finiteUniformProbabilityL2Data
    (ι : Type)
    [Fintype ι]
    [Nonempty ι] :
    FiniteStrictProbabilityL2Data ι where
  weight := fun _ : ι => (Fintype.card ι : ℝ)⁻¹
  weight_pos := by
    intro _i
    exact inv_pos.mpr (by exact_mod_cast Fintype.card_pos)
  weight_sum := by
    classical
    have hcard : (Fintype.card ι : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    simp [hcard]

@[simp] theorem finiteUniformProbabilityL2Data_weight
    (ι : Type)
    [Fintype ι]
    [Nonempty ι]
    (i : ι) :
    (finiteUniformProbabilityL2Data ι).weight i =
      (Fintype.card ι : ℝ)⁻¹ :=
  rfl

/-- An orthonormal basis identifies a finite-dimensional real Hilbert space
with the square-root coordinate carrier of any strict finite probability on
the same index type. -/
noncomputable def orthonormalBasisProbabilityL2Identification
    {ι : Type}
    {E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (P : FiniteStrictProbabilityL2Data ι)
    (b : OrthonormalBasis ι ℝ E) :
    RealHilbertLinearIsometricIdentification E
      (FiniteProbabilityL2Carrier ι) where
  forward := b.repr.toLinearIsometry
  inverse := b.repr.symm.toLinearIsometry
  forward_inverse := b.repr.apply_symm_apply
  inverse_forward := b.repr.symm_apply_apply

/-- Pointwise multiplication on finite probability `L²` square-root
coordinates. -/
noncomputable def finiteProbabilityCoordinateMultiplicationOperator
    {ι : Type}
    [Fintype ι]
    (P : FiniteStrictProbabilityL2Data ι)
    (a : ι → ℝ) :
    FiniteProbabilityL2Carrier ι →L[ℝ]
      FiniteProbabilityL2Carrier ι :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 fun i : ι => a i * x i
      map_add' := by
        intro x y
        ext i
        change a i * (x i + y i) = a i * x i + a i * y i
        ring
      map_smul' := by
        intro c x
        ext i
        change a i * (c * x i) = c * (a i * x i)
        ring }

@[simp] theorem finiteProbabilityCoordinateMultiplicationOperator_apply
    {ι : Type}
    [Fintype ι]
    (P : FiniteStrictProbabilityL2Data ι)
    (a : ι → ℝ)
    (x : FiniteProbabilityL2Carrier ι)
    (i : ι) :
    finiteProbabilityCoordinateMultiplicationOperator P a x i =
      a i * x i :=
  rfl

/-- Conjugating a diagonal operator through its orthonormal-basis probability
coordinates gives literal pointwise multiplication. -/
theorem orthonormalBasisProbabilityL2Identification_transport_diagonal
    {ι : Type}
    {E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (P : FiniteStrictProbabilityL2Data ι)
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ) :
    (orthonormalBasisProbabilityL2Identification P b).transportOperator
        (orthonormalDiagonalOperator b a) =
      finiteProbabilityCoordinateMultiplicationOperator P a := by
  apply ContinuousLinearMap.ext
  intro y
  ext i
  rw [RealHilbertLinearIsometricIdentification.transportOperator_apply]
  change
    b.repr (orthonormalDiagonalOperator b a (b.repr.symm y)) i =
      a i * y i
  rw [b.repr_apply_apply]
  calc
    inner ℝ (b i)
        (orthonormalDiagonalOperator b a (b.repr.symm y)) =
      inner ℝ
        (orthonormalDiagonalOperator b a (b i))
        (b.repr.symm y) := by
          exact
            (orthonormalDiagonalOperator_isSymmetric
              b a (b i) (b.repr.symm y)).symm
    _ = inner ℝ (a i • b i) (b.repr.symm y) := by
      rw [orthonormalDiagonalOperator_apply_basis]
    _ = a i * inner ℝ (b i) (b.repr.symm y) := by
      rw [real_inner_smul_left]
    _ = a i * b.repr (b.repr.symm y) i := by
      rw [b.repr_apply_apply]
    _ = a i * y i := by
      rw [b.repr.apply_symm_apply]

/-- Audit-visible receipt for a finite probability `L²` coordinate
realization and a diagonal operator transported to pointwise multiplication. -/
structure FiniteProbabilityL2OrthonormalCoordinatePackage
    (ι : Type)
    (E : Type*)
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] where
  probability : FiniteStrictProbabilityL2Data ι
  basis : OrthonormalBasis ι ℝ E
  coefficient : ι → ℝ
  identification :
    RealHilbertLinearIsometricIdentification E
      (FiniteProbabilityL2Carrier ι)
  identification_eq_basis :
    identification =
      orthonormalBasisProbabilityL2Identification probability basis
  coordinateOperator :
    FiniteProbabilityL2Carrier ι →L[ℝ]
      FiniteProbabilityL2Carrier ι
  coordinateOperator_eq_pointwise :
    coordinateOperator =
      finiteProbabilityCoordinateMultiplicationOperator
        probability coefficient
  exactTransport :
    identification.transportOperator
        (orthonormalDiagonalOperator basis coefficient) =
      coordinateOperator

/-- Construct the generic finite-probability coordinate receipt. -/
noncomputable def finiteProbabilityL2OrthonormalCoordinatePackage
    (ι : Type)
    (E : Type*)
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (P : FiniteStrictProbabilityL2Data ι)
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ) :
    FiniteProbabilityL2OrthonormalCoordinatePackage ι E where
  probability := P
  basis := b
  coefficient := a
  identification :=
    orthonormalBasisProbabilityL2Identification P b
  identification_eq_basis := rfl
  coordinateOperator :=
    finiteProbabilityCoordinateMultiplicationOperator P a
  coordinateOperator_eq_pointwise := rfl
  exactTransport :=
    orthonormalBasisProbabilityL2Identification_transport_diagonal
      P b a

end

end MathlibAnalytic
end MGAP4D
