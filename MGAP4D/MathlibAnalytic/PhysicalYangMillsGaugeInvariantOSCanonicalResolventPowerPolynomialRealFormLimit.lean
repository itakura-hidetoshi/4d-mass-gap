import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalResolventPowers
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalFiniteResolventAlgebraRealFormLimit
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace LinearPMap
open StandardRealHilbertComplexification

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- The finite-time bounded real operator represented by a finite real
polynomial in one admissible rescaled-defect resolvent. -/
noncomputable def VacuumSemigroupGapSlope.admissibleRescaledDefectResolventFinsetPolynomial
    {T : P.StronglyContinuousPhysicalSemigroup}
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    {lambda : ℝ}
    (hlambda : lambda < G.mass / 2)
    (s : Finset ℕ)
    (c : ℕ → ℝ) :
    P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert :=
  s.sum (fun n => c n •
    ((G.admissibleRescaledDefectResolvent
      hInnerSymmetric tau hlambda) ^ n))

/-- The corresponding continuum bounded real resolvent polynomial. -/
noncomputable def VacuumSemigroupGapSlope.continuumResolventFinsetPolynomial
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ}
    (hlambda : lambda < G.mass / 2)
    (s : Finset ℕ)
    (c : ℕ → ℝ) :
    P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert :=
  s.sum (fun n => c n •
    ((G.vacuumOrthogonalContinuumRealResolvent
      T hP hInnerSymmetric hSelf hlambda) ^ n))

/-- Every finite real polynomial in one below-half-mass resolvent converges
pointwise strongly after canonical diagonal complexification on the full
standard complexification. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventFinsetPolynomialDiagonalComplexification_tendsto_continuum
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ}
    (hlambda : lambda < G.mass / 2)
    (s : Finset ℕ)
    (c : ℕ → ℝ)
    (z : StandardRealHilbertComplexification P.VacuumOrthogonalHilbert) :
    Tendsto
      (fun tau : G.AdmissibleRescaledDefectTime =>
        diagonalComplexification
          (G.admissibleRescaledDefectResolventFinsetPolynomial
            hInnerSymmetric tau hlambda s c) z)
      G.admissibleRescaledDefectTimeFilter
      (𝓝
        (diagonalComplexification
          (G.continuumResolventFinsetPolynomial
            T hP hInnerSymmetric hSelf hlambda s c) z)) := by
  have hRe :
      Tendsto
        (fun tau : G.AdmissibleRescaledDefectTime =>
          G.admissibleRescaledDefectResolventFinsetPolynomial
            hInnerSymmetric tau hlambda s c z.1)
        G.admissibleRescaledDefectTimeFilter
        (𝓝
          (G.continuumResolventFinsetPolynomial
            T hP hInnerSymmetric hSelf hlambda s c z.1)) := by
    simpa [
      VacuumSemigroupGapSlope.admissibleRescaledDefectResolventFinsetPolynomial,
      VacuumSemigroupGapSlope.continuumResolventFinsetPolynomial] using
      G.admissibleRescaledDefectResolvent_finsetPolynomial_tendsto_continuumResolvent_finsetPolynomial
        T hP hInnerSymmetric hSelf hlambda s c z.1
  have hIm :
      Tendsto
        (fun tau : G.AdmissibleRescaledDefectTime =>
          G.admissibleRescaledDefectResolventFinsetPolynomial
            hInnerSymmetric tau hlambda s c z.2)
        G.admissibleRescaledDefectTimeFilter
        (𝓝
          (G.continuumResolventFinsetPolynomial
            T hP hInnerSymmetric hSelf hlambda s c z.2)) := by
    simpa [
      VacuumSemigroupGapSlope.admissibleRescaledDefectResolventFinsetPolynomial,
      VacuumSemigroupGapSlope.continuumResolventFinsetPolynomial] using
      G.admissibleRescaledDefectResolvent_finsetPolynomial_tendsto_continuumResolvent_finsetPolynomial
        T hP hInnerSymmetric hSelf hlambda s c z.2
  have hReOfReal :
      Tendsto
        (fun tau : G.AdmissibleRescaledDefectTime =>
          ofReal
            (G.admissibleRescaledDefectResolventFinsetPolynomial
              hInnerSymmetric tau hlambda s c z.1))
        G.admissibleRescaledDefectTimeFilter
        (𝓝
          (ofReal
            (G.continuumResolventFinsetPolynomial
              T hP hInnerSymmetric hSelf hlambda s c z.1))) := by
    simpa only [standardOfRealLinearIsometry_apply] using
      ((standardOfRealLinearIsometry
        (H := P.VacuumOrthogonalHilbert)).continuous.tendsto _).comp hRe
  have hImOfReal :
      Tendsto
        (fun tau : G.AdmissibleRescaledDefectTime =>
          ofReal
            (G.admissibleRescaledDefectResolventFinsetPolynomial
              hInnerSymmetric tau hlambda s c z.2))
        G.admissibleRescaledDefectTimeFilter
        (𝓝
          (ofReal
            (G.continuumResolventFinsetPolynomial
              T hP hInnerSymmetric hSelf hlambda s c z.2))) := by
    simpa only [standardOfRealLinearIsometry_apply] using
      ((standardOfRealLinearIsometry
        (H := P.VacuumOrthogonalHilbert)).continuous.tendsto _).comp hIm
  have hComplex := hReOfReal.add (hImOfReal.const_smul Complex.I)
  have hSource :
      (fun tau : G.AdmissibleRescaledDefectTime =>
        diagonalComplexification
          (G.admissibleRescaledDefectResolventFinsetPolynomial
            hInnerSymmetric tau hlambda s c) z) =
      (fun tau : G.AdmissibleRescaledDefectTime =>
        ofReal
            (G.admissibleRescaledDefectResolventFinsetPolynomial
              hInnerSymmetric tau hlambda s c z.1) +
          Complex.I • ofReal
            (G.admissibleRescaledDefectResolventFinsetPolynomial
              hInnerSymmetric tau hlambda s c z.2)) := by
    funext tau
    rw [diagonalComplexification_apply]
    exact decompose _
  have hTarget :
      diagonalComplexification
          (G.continuumResolventFinsetPolynomial
            T hP hInnerSymmetric hSelf hlambda s c) z =
        ofReal
            (G.continuumResolventFinsetPolynomial
              T hP hInnerSymmetric hSelf hlambda s c z.1) +
          Complex.I • ofReal
            (G.continuumResolventFinsetPolynomial
              T hP hInnerSymmetric hSelf hlambda s c z.2) := by
    rw [diagonalComplexification_apply]
    exact decompose _
  rw [hSource, hTarget]
  exact hComplex

/-- The continuum limit of every finite real polynomial in one resolvent remains
in the closed diagonal real-form star subalgebra. -/
theorem VacuumSemigroupGapSlope.continuumResolventFinsetPolynomialDiagonalComplexification_mem_realForm
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ}
    (hlambda : lambda < G.mass / 2)
    (s : Finset ℕ)
    (c : ℕ → ℝ) :
    diagonalComplexification
        (G.continuumResolventFinsetPolynomial
          T hP hInnerSymmetric hSelf hlambda s c) ∈
      diagonalComplexificationStarSubalgebra
        (H := P.VacuumOrthogonalHilbert) := by
  let F : G.AdmissibleRescaledDefectTime →
      diagonalComplexificationStarSubalgebra
        (H := P.VacuumOrthogonalHilbert) :=
    fun tau =>
      diagonalComplexificationStarAlgEquiv
        (H := P.VacuumOrthogonalHilbert)
        (G.admissibleRescaledDefectResolventFinsetPolynomial
          hInnerSymmetric tau hlambda s c)
  apply
    mem_diagonalComplexificationStarSubalgebra_of_tendsto_apply
      (H := P.VacuumOrthogonalHilbert)
      (l := G.admissibleRescaledDefectTimeFilter)
      F
      (diagonalComplexification
        (G.continuumResolventFinsetPolynomial
          T hP hInnerSymmetric hSelf hlambda s c))
  intro z
  simpa [F] using
    G.admissibleRescaledDefectResolventFinsetPolynomialDiagonalComplexification_tendsto_continuum
      T hP hInnerSymmetric hSelf hlambda s c z

/-- The bounded real operator underlying the complex strong limit of a finite
resolvent polynomial exists uniquely. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventFinsetPolynomialDiagonalComplexification_existsUnique_real_limit
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ}
    (hlambda : lambda < G.mass / 2)
    (s : Finset ℕ)
    (c : ℕ → ℝ) :
    ∃! R : P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert,
      diagonalComplexification R =
        diagonalComplexification
          (G.continuumResolventFinsetPolynomial
            T hP hInnerSymmetric hSelf hlambda s c) := by
  apply
    tendsto_diagonalComplexification_apply_existsUnique_real_limit
      (H := P.VacuumOrthogonalHilbert)
      (l := G.admissibleRescaledDefectTimeFilter)
      (f := fun tau : G.AdmissibleRescaledDefectTime =>
        G.admissibleRescaledDefectResolventFinsetPolynomial
          hInnerSymmetric tau hlambda s c)
      (X := diagonalComplexification
        (G.continuumResolventFinsetPolynomial
          T hP hInnerSymmetric hSelf hlambda s c))
  intro z
  exact
    G.admissibleRescaledDefectResolventFinsetPolynomialDiagonalComplexification_tendsto_continuum
      T hP hInnerSymmetric hSelf hlambda s c z

/-- Any real bounded operator producing the same complex pointwise strong limit
is exactly the corresponding continuum resolvent polynomial. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventFinsetPolynomial_real_limit_eq_continuum
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ}
    (hlambda : lambda < G.mass / 2)
    (s : Finset ℕ)
    (c : ℕ → ℝ)
    (R : P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert)
    (hR : ∀ z : StandardRealHilbertComplexification P.VacuumOrthogonalHilbert,
      Tendsto
        (fun tau : G.AdmissibleRescaledDefectTime =>
          diagonalComplexification
            (G.admissibleRescaledDefectResolventFinsetPolynomial
              hInnerSymmetric tau hlambda s c) z)
        G.admissibleRescaledDefectTimeFilter
        (𝓝 (diagonalComplexification R z))) :
    R = G.continuumResolventFinsetPolynomial
      T hP hInnerSymmetric hSelf hlambda s c := by
  have hComplex :
      diagonalComplexification R =
        diagonalComplexification
          (G.continuumResolventFinsetPolynomial
            T hP hInnerSymmetric hSelf hlambda s c) := by
    ext z
    exact tendsto_nhds_unique
      (hR z)
      (G.admissibleRescaledDefectResolventFinsetPolynomialDiagonalComplexification_tendsto_continuum
        T hP hInnerSymmetric hSelf hlambda s c z)
  apply
    (diagonalComplexificationLinearIsometry
      (H := P.VacuumOrthogonalHilbert)).injective
  simpa only [diagonalComplexificationLinearIsometry_apply] using hComplex

/-- Actual OS real-form strong-limit package for arbitrary finite real
polynomials in one below-half-mass resolvent. -/
theorem VacuumSemigroupGapSlope.canonicalResolventFinsetPolynomialRealFormStrongLimitPackage
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ}
    (hlambda : lambda < G.mass / 2)
    (s : Finset ℕ)
    (c : ℕ → ℝ) :
    (∀ z : StandardRealHilbertComplexification P.VacuumOrthogonalHilbert,
      Tendsto
        (fun tau : G.AdmissibleRescaledDefectTime =>
          diagonalComplexification
            (G.admissibleRescaledDefectResolventFinsetPolynomial
              hInnerSymmetric tau hlambda s c) z)
        G.admissibleRescaledDefectTimeFilter
        (𝓝
          (diagonalComplexification
            (G.continuumResolventFinsetPolynomial
              T hP hInnerSymmetric hSelf hlambda s c) z))) ∧
    diagonalComplexification
        (G.continuumResolventFinsetPolynomial
          T hP hInnerSymmetric hSelf hlambda s c) ∈
      diagonalComplexificationStarSubalgebra
        (H := P.VacuumOrthogonalHilbert) ∧
    ∃! R : P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert,
      diagonalComplexification R =
        diagonalComplexification
          (G.continuumResolventFinsetPolynomial
            T hP hInnerSymmetric hSelf hlambda s c) := by
  constructor
  · intro z
    exact
      G.admissibleRescaledDefectResolventFinsetPolynomialDiagonalComplexification_tendsto_continuum
        T hP hInnerSymmetric hSelf hlambda s c z
  constructor
  · exact
      G.continuumResolventFinsetPolynomialDiagonalComplexification_mem_realForm
        T hP hInnerSymmetric hSelf hlambda s c
  · exact
      G.admissibleRescaledDefectResolventFinsetPolynomialDiagonalComplexification_existsUnique_real_limit
        T hP hInnerSymmetric hSelf hlambda s c

/-- A single finite resolvent power, represented as a singleton polynomial. -/
noncomputable def VacuumSemigroupGapSlope.admissibleRescaledDefectResolventPower
    {T : P.StronglyContinuousPhysicalSemigroup}
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    {lambda : ℝ}
    (hlambda : lambda < G.mass / 2)
    (n : ℕ) :
    P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert :=
  G.admissibleRescaledDefectResolventFinsetPolynomial
    hInnerSymmetric tau hlambda {n} (fun _ => 1)

/-- The corresponding continuum finite resolvent power. -/
noncomputable def VacuumSemigroupGapSlope.continuumResolventPower
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ}
    (hlambda : lambda < G.mass / 2)
    (n : ℕ) :
    P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert :=
  G.continuumResolventFinsetPolynomial
    T hP hInnerSymmetric hSelf hlambda {n} (fun _ => 1)

@[simp] theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventPower_eq_pow
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    {lambda : ℝ}
    (hlambda : lambda < G.mass / 2)
    (n : ℕ) :
    G.admissibleRescaledDefectResolventPower
        hInnerSymmetric tau hlambda n =
      (G.admissibleRescaledDefectResolvent
        hInnerSymmetric tau hlambda) ^ n := by
  simp [
    VacuumSemigroupGapSlope.admissibleRescaledDefectResolventPower,
    VacuumSemigroupGapSlope.admissibleRescaledDefectResolventFinsetPolynomial]

@[simp] theorem VacuumSemigroupGapSlope.continuumResolventPower_eq_pow
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ}
    (hlambda : lambda < G.mass / 2)
    (n : ℕ) :
    G.continuumResolventPower
        T hP hInnerSymmetric hSelf hlambda n =
      (G.vacuumOrthogonalContinuumRealResolvent
        T hP hInnerSymmetric hSelf hlambda) ^ n := by
  simp [
    VacuumSemigroupGapSlope.continuumResolventPower,
    VacuumSemigroupGapSlope.continuumResolventFinsetPolynomial]

/-- Every finite repeated-shift resolvent power converges pointwise strongly
after canonical diagonal complexification. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventPowerDiagonalComplexification_tendsto_continuum
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ}
    (hlambda : lambda < G.mass / 2)
    (n : ℕ)
    (z : StandardRealHilbertComplexification P.VacuumOrthogonalHilbert) :
    Tendsto
      (fun tau : G.AdmissibleRescaledDefectTime =>
        diagonalComplexification
          (G.admissibleRescaledDefectResolventPower
            hInnerSymmetric tau hlambda n) z)
      G.admissibleRescaledDefectTimeFilter
      (𝓝
        (diagonalComplexification
          (G.continuumResolventPower
            T hP hInnerSymmetric hSelf hlambda n) z)) := by
  simpa [
    VacuumSemigroupGapSlope.admissibleRescaledDefectResolventPower,
    VacuumSemigroupGapSlope.continuumResolventPower] using
    G.admissibleRescaledDefectResolventFinsetPolynomialDiagonalComplexification_tendsto_continuum
      T hP hInnerSymmetric hSelf hlambda {n} (fun _ => 1) z

/-- Every continuum finite repeated-shift resolvent power remains in the closed
diagonal real-form star subalgebra. -/
theorem VacuumSemigroupGapSlope.continuumResolventPowerDiagonalComplexification_mem_realForm
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ}
    (hlambda : lambda < G.mass / 2)
    (n : ℕ) :
    diagonalComplexification
        (G.continuumResolventPower
          T hP hInnerSymmetric hSelf hlambda n) ∈
      diagonalComplexificationStarSubalgebra
        (H := P.VacuumOrthogonalHilbert) := by
  simpa [VacuumSemigroupGapSlope.continuumResolventPower] using
    G.continuumResolventFinsetPolynomialDiagonalComplexification_mem_realForm
      T hP hInnerSymmetric hSelf hlambda {n} (fun _ => 1)

/-- The bounded real operator underlying the complex strong limit of every
finite repeated-shift resolvent power exists uniquely. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventPowerDiagonalComplexification_existsUnique_real_limit
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ}
    (hlambda : lambda < G.mass / 2)
    (n : ℕ) :
    ∃! R : P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert,
      diagonalComplexification R =
        diagonalComplexification
          (G.continuumResolventPower
            T hP hInnerSymmetric hSelf hlambda n) := by
  simpa [VacuumSemigroupGapSlope.continuumResolventPower] using
    G.admissibleRescaledDefectResolventFinsetPolynomialDiagonalComplexification_existsUnique_real_limit
      T hP hInnerSymmetric hSelf hlambda {n} (fun _ => 1)

/-- Any real bounded operator producing the same complex pointwise strong limit
is exactly the corresponding continuum finite resolvent power. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventPower_real_limit_eq_continuum
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ}
    (hlambda : lambda < G.mass / 2)
    (n : ℕ)
    (R : P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert)
    (hR : ∀ z : StandardRealHilbertComplexification P.VacuumOrthogonalHilbert,
      Tendsto
        (fun tau : G.AdmissibleRescaledDefectTime =>
          diagonalComplexification
            (G.admissibleRescaledDefectResolventPower
              hInnerSymmetric tau hlambda n) z)
        G.admissibleRescaledDefectTimeFilter
        (𝓝 (diagonalComplexification R z))) :
    R = G.continuumResolventPower
      T hP hInnerSymmetric hSelf hlambda n := by
  apply
    G.admissibleRescaledDefectResolventFinsetPolynomial_real_limit_eq_continuum
      T hP hInnerSymmetric hSelf hlambda {n} (fun _ => 1) R
  intro z
  simpa [VacuumSemigroupGapSlope.admissibleRescaledDefectResolventPower] using
    hR z

/-- Actual OS real-form strong-limit package for every finite repeated-shift
resolvent power. -/
theorem VacuumSemigroupGapSlope.canonicalResolventPowerRealFormStrongLimitPackage
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ}
    (hlambda : lambda < G.mass / 2)
    (n : ℕ) :
    (∀ z : StandardRealHilbertComplexification P.VacuumOrthogonalHilbert,
      Tendsto
        (fun tau : G.AdmissibleRescaledDefectTime =>
          diagonalComplexification
            (G.admissibleRescaledDefectResolventPower
              hInnerSymmetric tau hlambda n) z)
        G.admissibleRescaledDefectTimeFilter
        (𝓝
          (diagonalComplexification
            (G.continuumResolventPower
              T hP hInnerSymmetric hSelf hlambda n) z))) ∧
    diagonalComplexification
        (G.continuumResolventPower
          T hP hInnerSymmetric hSelf hlambda n) ∈
      diagonalComplexificationStarSubalgebra
        (H := P.VacuumOrthogonalHilbert) ∧
    ∃! R : P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert,
      diagonalComplexification R =
        diagonalComplexification
          (G.continuumResolventPower
            T hP hInnerSymmetric hSelf hlambda n) := by
  constructor
  · intro z
    exact
      G.admissibleRescaledDefectResolventPowerDiagonalComplexification_tendsto_continuum
        T hP hInnerSymmetric hSelf hlambda n z
  constructor
  · exact
      G.continuumResolventPowerDiagonalComplexification_mem_realForm
        T hP hInnerSymmetric hSelf hlambda n
  · exact
      G.admissibleRescaledDefectResolventPowerDiagonalComplexification_existsUnique_real_limit
        T hP hInnerSymmetric hSelf hlambda n

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
