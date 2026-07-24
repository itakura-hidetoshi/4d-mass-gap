import MGAP4D.MathlibAnalytic.StandardRealHilbertSelfAdjointBoundedTransformInverseSquareRootNaturalDomain
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped InnerProductSpace

/-- The strictly algebraic positive-square-root boundary for the bounded inverse of `1 + A²`.

The range condition in `D(A)` is omitted.  It is generated below from self-adjointness,
`R² = K`, the shifted-square energy identity, density of the range of `R`, and closedness of `A`. -/
structure StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseAlgebraicSquareRootData
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A) where
  squareRoot : H →L[ℝ] H
  selfAdjoint : IsSelfAdjoint squareRoot
  quadraticForm_nonnegative :
    ∀ x : H, 0 ≤ inner ℝ (squareRoot x) x
  squareRoot_sq :
    ∀ x : H, squareRoot (squareRoot x) = K.inverse x

/-- The bounded inverse, bundled as a linear map into the natural shifted-square domain. -/
def StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData.inverseToShiftedSquareDomain
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A) :
    H →ₗ[ℝ] (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A).domain where
  toFun x := ⟨K.inverse x, K.range_mem_shiftedSquare_domain x⟩
  map_add' x y := by
    apply Subtype.ext
    exact K.inverse.map_add x y
  map_smul' c x := by
    apply Subtype.ext
    exact K.inverse.map_smul c x

@[simp]
theorem StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData.inverseToShiftedSquareDomain_coe
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A)
    (x : H) :
    (K.inverseToShiftedSquareDomain x : H) = K.inverse x :=
  rfl

/-- Transport the bounded inverse into the subtype natural square domain. -/
def StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData.inverseToSquareDomain
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A) :
    H →ₗ[ℝ] standardRealHilbertSelfAdjointSquareDomain A :=
  (standardRealHilbertSelfAdjointSquareDomainEquivAmbient A).symm.toLinearMap.comp
    K.inverseToShiftedSquareDomain

/-- Forget one level of square-domain regularity and regard the inverse as landing in `D(A)`. -/
def StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData.inverseToOriginalDomain
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A) :
    H →ₗ[ℝ] A.domain :=
  (standardRealHilbertSelfAdjointSquareDomain A).subtype.comp
    K.inverseToSquareDomain

@[simp]
theorem StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData.inverseToOriginalDomain_coe
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A)
    (x : H) :
    ((K.inverseToOriginalDomain x : A.domain) : H) = K.inverse x := by
  calc
    ((K.inverseToOriginalDomain x : A.domain) : H) =
        ((standardRealHilbertSelfAdjointSquareDomainEquivAmbient A
          (K.inverseToSquareDomain x) :
            standardRealHilbertSelfAdjointAmbientSquareDomain A) : H) := by
      symm
      exact
        standardRealHilbertSelfAdjointSquareDomainEquivAmbient_coe A
          (K.inverseToSquareDomain x)
    _ = (K.inverseToShiftedSquareDomain x : H) := by
      change
        ((standardRealHilbertSelfAdjointSquareDomainEquivAmbient A
          ((standardRealHilbertSelfAdjointSquareDomainEquivAmbient A).symm
            (K.inverseToShiftedSquareDomain x)) :
            standardRealHilbertSelfAdjointAmbientSquareDomain A) : H) = _
      rw [LinearEquiv.apply_symm_apply]
    _ = K.inverse x := rfl

/-- Apply `A` to the already square-domain-valued bounded inverse. -/
def StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData.inverseOriginalAction
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A) :
    H →ₗ[ℝ] H :=
  A.toFun.comp K.inverseToOriginalDomain

@[simp]
theorem StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData.inverseOriginalAction_apply
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A)
    (x : H) :
    K.inverseOriginalAction x = A (K.inverseToOriginalDomain x) :=
  rfl

/-- The exact right-inverse law makes the bounded inverse injective. -/
theorem StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData.inverse_injective
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A) :
    Function.Injective K.inverse := by
  intro x y hxy
  have hDomain :
      K.inverseToShiftedSquareDomain x = K.inverseToShiftedSquareDomain y := by
    apply Subtype.ext
    exact hxy
  calc
    x = standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A
          (K.inverseToShiftedSquareDomain x) := by
      symm
      simpa [StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData.inverseToShiftedSquareDomain]
        using K.shiftedSquare_inverse x
    _ = standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A
          (K.inverseToShiftedSquareDomain y) :=
      congrArg (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A) hDomain
    _ = y := by
      simpa [StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData.inverseToShiftedSquareDomain]
        using K.shiftedSquare_inverse y

/-- The square root is injective because its square is the injective bounded inverse. -/
theorem StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseAlgebraicSquareRootData.squareRoot_injective
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    {K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A}
    (R : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseAlgebraicSquareRootData K) :
    Function.Injective R.squareRoot := by
  intro x y hxy
  apply K.inverse_injective
  rw [← R.squareRoot_sq x, ← R.squareRoot_sq y, hxy]

/-- A bounded self-adjoint injective operator has dense range. -/
theorem StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseAlgebraicSquareRootData.squareRoot_denseRange
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    {K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A}
    (R : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseAlgebraicSquareRootData K) :
    DenseRange R.squareRoot := by
  have hAdjoint : R.squareRoot.adjoint = R.squareRoot :=
    ContinuousLinearMap.isSelfAdjoint_iff'.mp R.selfAdjoint
  have hKer : R.squareRoot.ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr R.squareRoot_injective
  have hOrthogonal : R.squareRoot.rangeᗮ = ⊥ := by
    rw [R.squareRoot.orthogonal_range, hAdjoint, hKer]
  have hClosure : R.squareRoot.range.topologicalClosure = ⊤ :=
    (Submodule.topologicalClosure_eq_top_iff).2 hOrthogonal
  show Dense (Set.range R.squareRoot)
  rw [dense_iff_closure_eq]
  have hRange : Set.range R.squareRoot = (R.squareRoot.range : Set H) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, hx⟩
  rw [hRange, ← Submodule.topologicalClosure_coe, hClosure]
  rfl

/-- The shifted-square energy identity controls `A Kx` by `Rx`. -/
theorem StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseAlgebraicSquareRootData.inverseOriginalAction_norm_le_squareRoot
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    {K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A}
    (R : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseAlgebraicSquareRootData K)
    (core : RealHilbertSelfAdjointCore A)
    (x : H) :
    ‖K.inverseOriginalAction x‖ ≤ ‖R.squareRoot x‖ := by
  let y : standardRealHilbertSelfAdjointSquareDomain A := K.inverseToSquareDomain x
  have hShifted :
      standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A
          (standardRealHilbertSelfAdjointSquareDomainEquivAmbient A y) = x := by
    have hy :
        standardRealHilbertSelfAdjointSquareDomainEquivAmbient A y =
          K.inverseToShiftedSquareDomain x := by
      dsimp [y,
        StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData.inverseToSquareDomain]
      exact LinearEquiv.apply_symm_apply _ _
    rw [hy]
    simpa [StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData.inverseToShiftedSquareDomain]
      using K.shiftedSquare_inverse x
  have hQuadratic :=
    standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare_quadraticForm_identity
      A core y
  rw [hShifted,
    standardRealHilbertSelfAdjointSquareDomainEquivAmbient_coe] at hQuadratic
  have hQuadratic' :
      inner ℝ x (K.inverse x) =
        ‖K.inverse x‖ ^ 2 + ‖K.inverseOriginalAction x‖ ^ 2 := by
    simpa [y,
      StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData.inverseToOriginalDomain,
      StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData.inverseOriginalAction]
      using hQuadratic
  have hAdjoint : R.squareRoot.adjoint = R.squareRoot :=
    ContinuousLinearMap.isSelfAdjoint_iff'.mp R.selfAdjoint
  have hInner :
      inner ℝ x (K.inverse x) = ‖R.squareRoot x‖ ^ 2 := by
    rw [← R.squareRoot_sq x]
    calc
      inner ℝ x (R.squareRoot (R.squareRoot x)) =
          inner ℝ x (R.squareRoot.adjoint (R.squareRoot x)) := by
        rw [hAdjoint]
      _ = inner ℝ (R.squareRoot x) (R.squareRoot x) :=
        ContinuousLinearMap.adjoint_inner_right
          R.squareRoot x (R.squareRoot x)
      _ = ‖R.squareRoot x‖ ^ 2 :=
        real_inner_self_eq_norm_sq (R.squareRoot x)
  have hsq : ‖K.inverseOriginalAction x‖ ^ 2 ≤ ‖R.squareRoot x‖ ^ 2 := by
    rw [hInner] at hQuadratic'
    nlinarith [sq_nonneg ‖K.inverse x‖]
  nlinarith [norm_nonneg (K.inverseOriginalAction x), norm_nonneg (R.squareRoot x)]

/-- Extend the densely defined action `R x ↦ A K x` to a bounded operator on all of `H`. -/
noncomputable def StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseAlgebraicSquareRootData.extendedOriginalAction
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    {K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A}
    (R : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseAlgebraicSquareRootData K) :
    H →L[ℝ] H :=
  K.inverseOriginalAction.extendOfNorm R.squareRoot.toLinearMap

/-- The extended action agrees with `A K` on the dense range of `R`. -/
theorem StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseAlgebraicSquareRootData.extendedOriginalAction_apply_squareRoot
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    {K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A}
    (R : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseAlgebraicSquareRootData K)
    (core : RealHilbertSelfAdjointCore A)
    (x : H) :
    R.extendedOriginalAction (R.squareRoot x) = K.inverseOriginalAction x := by
  exact LinearMap.extendOfNorm_eq
    (f := K.inverseOriginalAction)
    (e := R.squareRoot.toLinearMap)
    R.squareRoot_denseRange
    ⟨1, fun z => by
      simpa only [one_mul] using R.inverseOriginalAction_norm_le_squareRoot core z⟩
    x

/-- Closedness of `A` upgrades the square law to the natural regularity
`R(H) ⊆ D(A)`. -/
theorem StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseAlgebraicSquareRootData.range_mem_original_domain
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    {K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A}
    (R : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseAlgebraicSquareRootData K)
    (core : RealHilbertSelfAdjointCore A)
    (x : H) :
    R.squareRoot x ∈ A.domain := by
  let D : H →L[ℝ] H := R.extendedOriginalAction
  have hClosed :
      IsClosed {z : H | (R.squareRoot z, D z) ∈ A.graph} := by
    change IsClosed
      ((fun z : H => (R.squareRoot z, D z)) ⁻¹' (A.graph : Set (H × H)))
    exact core.selfAdjoint.isClosed.preimage
      (R.squareRoot.continuous.prod_mk D.continuous)
  have hGraph : ∀ z : H, (R.squareRoot z, D z) ∈ A.graph := by
    exact R.squareRoot_denseRange.induction
      (fun z hz => by
        rcases hz with ⟨w, rfl⟩
        have hD : D (R.squareRoot w) = K.inverseOriginalAction w := by
          exact R.extendedOriginalAction_apply_squareRoot core w
        rw [R.squareRoot_sq w, hD]
        simpa only [
          StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData.inverseToOriginalDomain_coe,
          StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData.inverseOriginalAction_apply]
          using A.mem_graph (K.inverseToOriginalDomain w))
      hClosed
  exact A.mem_domain_of_mem_graph (hGraph x)

/-- The algebraic positive square root reconstructs the natural-domain square-root data. -/
def StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseAlgebraicSquareRootData.toNaturalDomainSquareRootData
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    {K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A}
    (R : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseAlgebraicSquareRootData K)
    (core : RealHilbertSelfAdjointCore A) :
    StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseNaturalDomainSquareRootData K where
  squareRoot := R.squareRoot
  selfAdjoint := R.selfAdjoint
  quadraticForm_nonnegative := R.quadraticForm_nonnegative
  range_mem_original_domain := R.range_mem_original_domain core
  squareRoot_sq := R.squareRoot_sq

/-- Uniform construction of algebraic positive square roots; domain regularity is not residual. -/
structure StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseAlgebraicSquareRootDataConstructor where
  construct :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      (A : H →ₗ.[ℝ] H)
      (core : RealHilbertSelfAdjointCore A)
      (K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A),
        StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseAlgebraicSquareRootData K

/-- Forget the generated domain proof and recover the natural-domain constructor. -/
def StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseAlgebraicSquareRootDataConstructor.toNaturalDomainSquareRootDataConstructor
    (C : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseAlgebraicSquareRootDataConstructor) :
    StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseNaturalDomainSquareRootDataConstructor where
  construct := fun A core K => (C.construct A core K).toNaturalDomainSquareRootData core

end

end MathlibAnalytic
end MGAP4D
