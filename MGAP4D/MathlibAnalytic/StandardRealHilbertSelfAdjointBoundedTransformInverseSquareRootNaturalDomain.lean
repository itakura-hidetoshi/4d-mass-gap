import MGAP4D.MathlibAnalytic.StandardRealHilbertSelfAdjointBoundedTransformShiftedSquareGraphRieszVariationalSolution
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped InnerProductSpace

/-- A mathematically natural positive square-root boundary for the bounded inverse of
`1 + A²`.

Unlike the preceding square-root certificate, this structure asks only for the standard
regularity of `(1 + A²)⁻¹ᐟ²`, namely range in `D(A)`.  Membership of the second iterate in
the shifted-square domain is generated from `R² = K` and the already-proved range law for
`K = (1 + A²)⁻¹`. -/
structure StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseNaturalDomainSquareRootData
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A) where
  squareRoot : H →L[ℝ] H
  selfAdjoint : IsSelfAdjoint squareRoot
  quadraticForm_nonnegative :
    ∀ x : H, 0 ≤ inner ℝ (squareRoot x) x
  range_mem_original_domain :
    ∀ x : H, squareRoot x ∈ A.domain
  squareRoot_sq :
    ∀ x : H, squareRoot (squareRoot x) = K.inverse x

/-- The second iterate of the natural-domain square root lies in the shifted-square domain.
No range assumption on the first iterate in `D(A²)` is needed. -/
theorem StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseNaturalDomainSquareRootData.iterated_range_mem_shiftedSquare_domain
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    {K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A}
    (R : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseNaturalDomainSquareRootData K)
    (x : H) :
    R.squareRoot (R.squareRoot x) ∈
      (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A).domain := by
  rw [R.squareRoot_sq x]
  exact K.range_mem_shiftedSquare_domain x

/-- The shifted-square inverse-square-root law follows from `R² = K` and the right-inverse
law for `K`. -/
theorem StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseNaturalDomainSquareRootData.shiftedSquare_squareRoot_sq
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    {K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A}
    (R : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseNaturalDomainSquareRootData K)
    (x : H) :
    standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A
        ⟨R.squareRoot (R.squareRoot x),
          R.iterated_range_mem_shiftedSquare_domain x⟩ =
      x := by
  have hDomainEq :
      (⟨R.squareRoot (R.squareRoot x),
          R.iterated_range_mem_shiftedSquare_domain x⟩ :
        (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A).domain) =
      ⟨K.inverse x, K.range_mem_shiftedSquare_domain x⟩ := by
    apply Subtype.ext
    exact R.squareRoot_sq x
  rw [hDomainEq]
  exact K.shiftedSquare_inverse x

/-- The bounded inverse acts on an `A`-eigenvector by the scalar `(1 + E²)⁻¹`.
This uses only the exact shifted-square right-inverse law and injectivity of the canonical
shifted square. -/
theorem StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData.inverse_eigenvector_evaluation
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A)
    (core : RealHilbertSelfAdjointCore A)
    {E : ℝ} (x : A.domain)
    (hE : A x = E • (x : H)) :
    K.inverse (x : H) = (1 / (1 + E ^ 2)) • (x : H) := by
  let lambda : ℝ := 1 + E ^ 2
  have hlambdaPos : 0 < lambda := by
    dsimp [lambda]
    positivity
  have hlambdaNe : lambda ≠ 0 := ne_of_gt hlambdaPos
  let xSquare : standardRealHilbertSelfAdjointSquareDomain A :=
    ⟨x, standardRealHilbertSelfAdjoint_eigenvector_mem_squareDomain A x hE⟩
  let xAmbient : standardRealHilbertSelfAdjointAmbientSquareDomain A :=
    standardRealHilbertSelfAdjointSquareDomainEquivAmbient A xSquare
  have hxAmbientCoe : (xAmbient : H) = (x : H) := by
    dsimp [xAmbient]
    exact standardRealHilbertSelfAdjointSquareDomainEquivAmbient_coe A xSquare
  have hShiftedSquareX :
      standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A xAmbient =
        lambda • (x : H) := by
    dsimp [xAmbient, lambda]
    rw [standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare_apply]
    exact
      standardRealHilbertSelfAdjointShiftedSquareAction_eigenvector_evaluation
        A x hE
  let candidate :
      (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A).domain :=
    (1 / lambda) • xAmbient
  have hShiftedSquareCandidate :
      standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A candidate =
        (x : H) := by
    dsimp [candidate]
    change
      (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A).toFun
          ((1 / lambda) • xAmbient) =
        (x : H)
    have hShiftedSquareX' :
        (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A).toFun xAmbient =
          lambda • (x : H) :=
      hShiftedSquareX
    calc
      (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A).toFun
          ((1 / lambda) • xAmbient) =
          (1 / lambda) •
            (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A).toFun
              xAmbient := by
        exact
          (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A).toFun.map_smul
            (1 / lambda) xAmbient
      _ = (x : H) := by
        rw [hShiftedSquareX']
        simp [smul_smul, hlambdaNe]
  let inversePoint :
      (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A).domain :=
    ⟨K.inverse (x : H), K.range_mem_shiftedSquare_domain (x : H)⟩
  have hShiftedSquareInversePoint :
      standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A inversePoint =
        (x : H) := by
    exact K.shiftedSquare_inverse (x : H)
  have hInversePointEq : inversePoint = candidate :=
    standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare_injective A core
      (hShiftedSquareInversePoint.trans hShiftedSquareCandidate.symm)
  have hCoe := congrArg
    (fun z : (standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquare A).domain =>
      (z : H)) hInversePointEq
  change K.inverse (x : H) = (1 / lambda) • (xAmbient : H) at hCoe
  rw [hxAmbientCoe] at hCoe
  simpa [lambda] using hCoe

/-- Self-adjointness of `R`, the square law `R² = K`, and the contraction of `K` generate
the pointwise contraction of the positive square root. -/
theorem StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseNaturalDomainSquareRootData.squareRoot_norm_apply_le
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    {K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A}
    (R : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseNaturalDomainSquareRootData K)
    (x : H) :
    ‖R.squareRoot x‖ ≤ ‖x‖ := by
  have hAdjoint : R.squareRoot.adjoint = R.squareRoot :=
    ContinuousLinearMap.isSelfAdjoint_iff'.mp R.selfAdjoint
  have hKApply : ‖K.inverse x‖ ≤ ‖x‖ := by
    calc
      ‖K.inverse x‖ ≤ ‖K.inverse‖ * ‖x‖ := K.inverse.le_opNorm x
      _ ≤ 1 * ‖x‖ :=
        mul_le_mul_of_nonneg_right K.norm_le_one (norm_nonneg x)
      _ = ‖x‖ := one_mul _
  have hInner :
      inner ℝ (R.squareRoot x) (R.squareRoot x) =
        inner ℝ x (R.squareRoot (R.squareRoot x)) := by
    calc
      inner ℝ (R.squareRoot x) (R.squareRoot x) =
          inner ℝ x (R.squareRoot.adjoint (R.squareRoot x)) := by
        symm
        exact ContinuousLinearMap.adjoint_inner_right
          R.squareRoot x (R.squareRoot x)
      _ = inner ℝ x (R.squareRoot (R.squareRoot x)) := by
        rw [hAdjoint]
  have hsq : ‖R.squareRoot x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    calc
      ‖R.squareRoot x‖ ^ 2 =
          inner ℝ (R.squareRoot x) (R.squareRoot x) :=
        (real_inner_self_eq_norm_sq (R.squareRoot x)).symm
      _ = inner ℝ x (R.squareRoot (R.squareRoot x)) := hInner
      _ = inner ℝ x (K.inverse x) := by rw [R.squareRoot_sq x]
      _ ≤ ‖x‖ * ‖K.inverse x‖ := real_inner_le_norm x (K.inverse x)
      _ ≤ ‖x‖ * ‖x‖ :=
        mul_le_mul_of_nonneg_left hKApply (norm_nonneg x)
      _ = ‖x‖ ^ 2 := by ring
  nlinarith [norm_nonneg (R.squareRoot x), norm_nonneg x]

/-- The operator-norm contraction of the natural-domain square root is theorem-generated. -/
theorem StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseNaturalDomainSquareRootData.squareRoot_norm_le_one
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    {K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A}
    (R : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseNaturalDomainSquareRootData K) :
    ‖R.squareRoot‖ ≤ 1 := by
  apply R.squareRoot.opNorm_le_bound zero_le_one
  intro x
  simpa using R.squareRoot_norm_apply_le x

/-- Quadratic-form nonnegativity selects the positive scalar branch on every eigenvector. -/
theorem StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseNaturalDomainSquareRootData.eigenvector_evaluation
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    {K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A}
    (R : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseNaturalDomainSquareRootData K)
    (core : RealHilbertSelfAdjointCore A)
    {E : ℝ} (x : A.domain)
    (hE : A x = E • (x : H)) :
    R.squareRoot (x : H) =
      (1 / Real.sqrt (1 + E ^ 2)) • (x : H) := by
  let lambda : ℝ := 1 + E ^ 2
  let s : ℝ := 1 / Real.sqrt lambda
  have hlambdaPos : 0 < lambda := by
    dsimp [lambda]
    positivity
  have hsPos : 0 < s := by
    dsimp [s]
    positivity
  have hsSq : s ^ 2 = 1 / lambda := by
    dsimp [s]
    rw [div_pow, one_pow, Real.sq_sqrt hlambdaPos.le]
  have hR2 :
      R.squareRoot (R.squareRoot (x : H)) =
        (1 / lambda) • (x : H) := by
    rw [R.squareRoot_sq]
    simpa [lambda] using K.inverse_eigenvector_evaluation core x hE
  let y : H := R.squareRoot (x : H) - s • (x : H)
  have hPlus : R.squareRoot y + s • y = 0 := by
    dsimp [y]
    rw [map_sub, map_smul, hR2]
    simp only [smul_sub, smul_smul]
    rw [← pow_two s, hsSq]
    abel
  have hRy : R.squareRoot y = -(s • y) :=
    eq_neg_of_add_eq_zero_left hPlus
  have hPositive := R.quadraticForm_nonnegative y
  rw [hRy, inner_neg_left] at hPositive
  have hNonposInner : inner ℝ (s • y) y ≤ 0 :=
    neg_nonneg.mp hPositive
  have hNonpos : s * ‖y‖ ^ 2 ≤ 0 := by
    calc
      s * ‖y‖ ^ 2 = inner ℝ (s • y) y := by
        rw [inner_smul_left, real_inner_self_eq_norm_sq]
        simp
      _ ≤ 0 := hNonposInner
  have hyNormSq : ‖y‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg ‖y‖]
  have hyNorm : ‖y‖ = 0 := by
    nlinarith [norm_nonneg y]
  have hy : y = 0 := norm_eq_zero.mp hyNorm
  dsimp [y] at hy
  have hResult : R.squareRoot (x : H) = s • (x : H) :=
    sub_eq_zero.mp hy
  simpa [s, lambda] using hResult

/-- Uniform construction of mathematically natural positive square roots of the already-generated
bounded shifted-square inverse. -/
structure StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseNaturalDomainSquareRootDataConstructor where
  construct :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      (A : H →ₗ.[ℝ] H)
      (core : RealHilbertSelfAdjointCore A)
      (K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A),
        StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseNaturalDomainSquareRootData K

/-- The coercive inverse and the natural-domain positive square root are now two independent
stages.  The first stage is generated by the graph-Riesz route; the second is the exact remaining
real-Hilbert positive-square-root boundary. -/
structure NaturalDomainSquareRootFactoredStandardRealHilbertSelfAdjointBoundedTransformConstructor where
  boundedInverse :
    StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseDataConstructor
  positiveSquareRoot :
    StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseNaturalDomainSquareRootDataConstructor

/-- Apply the two-stage natural-domain factorization to one self-adjoint operator. -/
def NaturalDomainSquareRootFactoredStandardRealHilbertSelfAdjointBoundedTransformConstructor.construct
    (P : NaturalDomainSquareRootFactoredStandardRealHilbertSelfAdjointBoundedTransformConstructor)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →ₗ.[ℝ] H)
    (core : RealHilbertSelfAdjointCore A) :
    StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseNaturalDomainSquareRootData
      (P.boundedInverse.construct A core) :=
  P.positiveSquareRoot.construct A core (P.boundedInverse.construct A core)

end

end MathlibAnalytic
end MGAP4D
