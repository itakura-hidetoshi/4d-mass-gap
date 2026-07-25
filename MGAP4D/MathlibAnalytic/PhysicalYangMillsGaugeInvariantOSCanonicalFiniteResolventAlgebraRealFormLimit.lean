import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalFiniteResolventAlgebra
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalRescaledDefectResolventRealFormLimit
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

/-- The finite-time bounded real operator represented by a finite real linear
combination of finite words in admissible rescaled-defect resolvents. -/
noncomputable def VacuumSemigroupGapSlope.admissibleRescaledDefectResolventFinsetWordSum
    {β : Type*}
    {T : P.StronglyContinuousPhysicalSemigroup}
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    (s : Finset β)
    (word : β → List G.BelowHalfMassShift)
    (c : β → ℝ) :
    P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert :=
  s.sum (fun b => c b •
    ContinuousLinearMap.orderedProduct
      (fun sigma : G.BelowHalfMassShift =>
        G.admissibleRescaledDefectResolvent
          hInnerSymmetric tau sigma.property)
      (word b))

/-- The continuum bounded real operator represented by the corresponding finite
real resolvent word-sum. -/
noncomputable def VacuumSemigroupGapSlope.continuumResolventFinsetWordSum
    {β : Type*}
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (s : Finset β)
    (word : β → List G.BelowHalfMassShift)
    (c : β → ℝ) :
    P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert :=
  s.sum (fun b => c b •
    ContinuousLinearMap.orderedProduct
      (fun sigma : G.BelowHalfMassShift =>
        G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf sigma.property)
      (word b))

/-- Every finite real resolvent word-sum converges pointwise strongly after
canonical diagonal complexification on the full standard complexification. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventFinsetWordSumDiagonalComplexification_tendsto_continuum
    {β : Type*}
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (s : Finset β)
    (word : β → List G.BelowHalfMassShift)
    (c : β → ℝ)
    (z : StandardRealHilbertComplexification P.VacuumOrthogonalHilbert) :
    Tendsto
      (fun tau : G.AdmissibleRescaledDefectTime =>
        diagonalComplexification
          (G.admissibleRescaledDefectResolventFinsetWordSum
            hInnerSymmetric tau s word c) z)
      G.admissibleRescaledDefectTimeFilter
      (𝓝
        (diagonalComplexification
          (G.continuumResolventFinsetWordSum
            T hP hInnerSymmetric hSelf s word c) z)) := by
  have hRe :
      Tendsto
        (fun tau : G.AdmissibleRescaledDefectTime =>
          G.admissibleRescaledDefectResolventFinsetWordSum
            hInnerSymmetric tau s word c z.1)
        G.admissibleRescaledDefectTimeFilter
        (𝓝
          (G.continuumResolventFinsetWordSum
            T hP hInnerSymmetric hSelf s word c z.1)) := by
    simpa [VacuumSemigroupGapSlope.admissibleRescaledDefectResolventFinsetWordSum,
      VacuumSemigroupGapSlope.continuumResolventFinsetWordSum] using
      G.admissibleRescaledDefectResolvent_finsetWordSum_tendsto_continuumResolvent_finsetWordSum
        T hP hInnerSymmetric hSelf s word c z.1
  have hIm :
      Tendsto
        (fun tau : G.AdmissibleRescaledDefectTime =>
          G.admissibleRescaledDefectResolventFinsetWordSum
            hInnerSymmetric tau s word c z.2)
        G.admissibleRescaledDefectTimeFilter
        (𝓝
          (G.continuumResolventFinsetWordSum
            T hP hInnerSymmetric hSelf s word c z.2)) := by
    simpa [VacuumSemigroupGapSlope.admissibleRescaledDefectResolventFinsetWordSum,
      VacuumSemigroupGapSlope.continuumResolventFinsetWordSum] using
      G.admissibleRescaledDefectResolvent_finsetWordSum_tendsto_continuumResolvent_finsetWordSum
        T hP hInnerSymmetric hSelf s word c z.2
  have hReOfReal :
      Tendsto
        (fun tau : G.AdmissibleRescaledDefectTime =>
          ofReal
            (G.admissibleRescaledDefectResolventFinsetWordSum
              hInnerSymmetric tau s word c z.1))
        G.admissibleRescaledDefectTimeFilter
        (𝓝
          (ofReal
            (G.continuumResolventFinsetWordSum
              T hP hInnerSymmetric hSelf s word c z.1))) := by
    simpa only [standardOfRealLinearIsometry_apply] using
      ((standardOfRealLinearIsometry
        (H := P.VacuumOrthogonalHilbert)).continuous.tendsto _).comp hRe
  have hImOfReal :
      Tendsto
        (fun tau : G.AdmissibleRescaledDefectTime =>
          ofReal
            (G.admissibleRescaledDefectResolventFinsetWordSum
              hInnerSymmetric tau s word c z.2))
        G.admissibleRescaledDefectTimeFilter
        (𝓝
          (ofReal
            (G.continuumResolventFinsetWordSum
              T hP hInnerSymmetric hSelf s word c z.2))) := by
    simpa only [standardOfRealLinearIsometry_apply] using
      ((standardOfRealLinearIsometry
        (H := P.VacuumOrthogonalHilbert)).continuous.tendsto _).comp hIm
  have hComplex := hReOfReal.add (hImOfReal.const_smul Complex.I)
  have hSource :
      (fun tau : G.AdmissibleRescaledDefectTime =>
        diagonalComplexification
          (G.admissibleRescaledDefectResolventFinsetWordSum
            hInnerSymmetric tau s word c) z) =
      (fun tau : G.AdmissibleRescaledDefectTime =>
        ofReal
            (G.admissibleRescaledDefectResolventFinsetWordSum
              hInnerSymmetric tau s word c z.1) +
          Complex.I • ofReal
            (G.admissibleRescaledDefectResolventFinsetWordSum
              hInnerSymmetric tau s word c z.2)) := by
    funext tau
    rw [diagonalComplexification_apply]
    exact decompose _
  have hTarget :
      diagonalComplexification
          (G.continuumResolventFinsetWordSum
            T hP hInnerSymmetric hSelf s word c) z =
        ofReal
            (G.continuumResolventFinsetWordSum
              T hP hInnerSymmetric hSelf s word c z.1) +
          Complex.I • ofReal
            (G.continuumResolventFinsetWordSum
              T hP hInnerSymmetric hSelf s word c z.2) := by
    rw [diagonalComplexification_apply]
    exact decompose _
  rw [hSource, hTarget]
  exact hComplex

/-- The continuum limit of every finite real resolvent word-sum remains in the
closed diagonal real-form star subalgebra. -/
theorem VacuumSemigroupGapSlope.continuumResolventFinsetWordSumDiagonalComplexification_mem_realForm
    {β : Type*}
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (s : Finset β)
    (word : β → List G.BelowHalfMassShift)
    (c : β → ℝ) :
    diagonalComplexification
        (G.continuumResolventFinsetWordSum
          T hP hInnerSymmetric hSelf s word c) ∈
      diagonalComplexificationStarSubalgebra
        (H := P.VacuumOrthogonalHilbert) := by
  let F : G.AdmissibleRescaledDefectTime →
      diagonalComplexificationStarSubalgebra
        (H := P.VacuumOrthogonalHilbert) :=
    fun tau =>
      diagonalComplexificationStarAlgEquiv
        (H := P.VacuumOrthogonalHilbert)
        (G.admissibleRescaledDefectResolventFinsetWordSum
          hInnerSymmetric tau s word c)
  apply
    mem_diagonalComplexificationStarSubalgebra_of_tendsto_apply
      (H := P.VacuumOrthogonalHilbert)
      (l := G.admissibleRescaledDefectTimeFilter)
      F
      (diagonalComplexification
        (G.continuumResolventFinsetWordSum
          T hP hInnerSymmetric hSelf s word c))
  intro z
  simpa [F] using
    G.admissibleRescaledDefectResolventFinsetWordSumDiagonalComplexification_tendsto_continuum
      T hP hInnerSymmetric hSelf s word c z

/-- The bounded real operator underlying the complex strong limit of a finite
resolvent word-sum exists uniquely. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventFinsetWordSumDiagonalComplexification_existsUnique_real_limit
    {β : Type*}
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (s : Finset β)
    (word : β → List G.BelowHalfMassShift)
    (c : β → ℝ) :
    ∃! R : P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert,
      diagonalComplexification R =
        diagonalComplexification
          (G.continuumResolventFinsetWordSum
            T hP hInnerSymmetric hSelf s word c) := by
  apply
    tendsto_diagonalComplexification_apply_existsUnique_real_limit
      (H := P.VacuumOrthogonalHilbert)
      (l := G.admissibleRescaledDefectTimeFilter)
      (f := fun tau : G.AdmissibleRescaledDefectTime =>
        G.admissibleRescaledDefectResolventFinsetWordSum
          hInnerSymmetric tau s word c)
      (X := diagonalComplexification
        (G.continuumResolventFinsetWordSum
          T hP hInnerSymmetric hSelf s word c))
  intro z
  exact
    G.admissibleRescaledDefectResolventFinsetWordSumDiagonalComplexification_tendsto_continuum
      T hP hInnerSymmetric hSelf s word c z

/-- Any real bounded operator producing the same complex pointwise strong limit
is exactly the continuum finite resolvent word-sum. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventFinsetWordSum_real_limit_eq_continuum
    {β : Type*}
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (s : Finset β)
    (word : β → List G.BelowHalfMassShift)
    (c : β → ℝ)
    (R : P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert)
    (hR : ∀ z : StandardRealHilbertComplexification P.VacuumOrthogonalHilbert,
      Tendsto
        (fun tau : G.AdmissibleRescaledDefectTime =>
          diagonalComplexification
            (G.admissibleRescaledDefectResolventFinsetWordSum
              hInnerSymmetric tau s word c) z)
        G.admissibleRescaledDefectTimeFilter
        (𝓝 (diagonalComplexification R z))) :
    R = G.continuumResolventFinsetWordSum
      T hP hInnerSymmetric hSelf s word c := by
  have hComplex :
      diagonalComplexification R =
        diagonalComplexification
          (G.continuumResolventFinsetWordSum
            T hP hInnerSymmetric hSelf s word c) := by
    ext z
    exact tendsto_nhds_unique
      (hR z)
      (G.admissibleRescaledDefectResolventFinsetWordSumDiagonalComplexification_tendsto_continuum
        T hP hInnerSymmetric hSelf s word c z)
  apply
    (diagonalComplexificationLinearIsometry
      (H := P.VacuumOrthogonalHilbert)).injective
  simpa only [diagonalComplexificationLinearIsometry_apply] using hComplex

/-- Actual finite resolvent-algebra real-form strong-limit package.  It combines
full-complexification pointwise convergence, preservation of the diagonal real
form, and unique recovery of the underlying continuum bounded real operator. -/
theorem VacuumSemigroupGapSlope.canonicalFiniteResolventAlgebraRealFormStrongLimitPackage
    {β : Type*}
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (s : Finset β)
    (word : β → List G.BelowHalfMassShift)
    (c : β → ℝ) :
    (∀ z : StandardRealHilbertComplexification P.VacuumOrthogonalHilbert,
      Tendsto
        (fun tau : G.AdmissibleRescaledDefectTime =>
          diagonalComplexification
            (G.admissibleRescaledDefectResolventFinsetWordSum
              hInnerSymmetric tau s word c) z)
        G.admissibleRescaledDefectTimeFilter
        (𝓝
          (diagonalComplexification
            (G.continuumResolventFinsetWordSum
              T hP hInnerSymmetric hSelf s word c) z))) ∧
    diagonalComplexification
        (G.continuumResolventFinsetWordSum
          T hP hInnerSymmetric hSelf s word c) ∈
      diagonalComplexificationStarSubalgebra
        (H := P.VacuumOrthogonalHilbert) ∧
    ∃! R : P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert,
      diagonalComplexification R =
        diagonalComplexification
          (G.continuumResolventFinsetWordSum
            T hP hInnerSymmetric hSelf s word c) := by
  constructor
  · intro z
    exact
      G.admissibleRescaledDefectResolventFinsetWordSumDiagonalComplexification_tendsto_continuum
        T hP hInnerSymmetric hSelf s word c z
  constructor
  · exact
      G.continuumResolventFinsetWordSumDiagonalComplexification_mem_realForm
        T hP hInnerSymmetric hSelf s word c
  · exact
      G.admissibleRescaledDefectResolventFinsetWordSumDiagonalComplexification_existsUnique_real_limit
        T hP hInnerSymmetric hSelf s word c

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
