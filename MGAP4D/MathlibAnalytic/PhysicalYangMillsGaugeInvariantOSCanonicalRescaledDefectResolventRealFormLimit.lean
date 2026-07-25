import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalOperatorLimitPackage
import MGAP4D.MathlibAnalytic.StandardRealHilbertDiagonalStrongOperatorClosedness
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

/-- The diagonal complexifications of the admissible finite-time real resolvents
converge pointwise strongly on the full standard complexification to the diagonal
complexification of the continuum real resolvent.  The proof uses the existing
real convergence separately on the real and imaginary coordinates. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectDiagonalComplexification_tendsto_continuumResolvent
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ}
    (hlambda : lambda < G.mass / 2)
    (z : StandardRealHilbertComplexification P.VacuumOrthogonalHilbert) :
    Tendsto
      (fun tau : G.AdmissibleRescaledDefectTime =>
        diagonalComplexification
          (G.admissibleRescaledDefectResolvent
            hInnerSymmetric tau hlambda) z)
      G.admissibleRescaledDefectTimeFilter
      (𝓝
        (diagonalComplexification
          (G.vacuumOrthogonalContinuumRealResolvent
            T hP hInnerSymmetric hSelf hlambda) z)) := by
  have hRe :=
    G.admissibleRescaledDefectResolvent_tendsto_continuumResolvent
      T hP hInnerSymmetric hSelf hlambda z.1
  have hIm :=
    G.admissibleRescaledDefectResolvent_tendsto_continuumResolvent
      T hP hInnerSymmetric hSelf hlambda z.2
  have hReOfReal :
      Tendsto
        (fun tau : G.AdmissibleRescaledDefectTime =>
          ofReal
            (G.admissibleRescaledDefectResolvent
              hInnerSymmetric tau hlambda z.1))
        G.admissibleRescaledDefectTimeFilter
        (𝓝
          (ofReal
            (G.vacuumOrthogonalContinuumRealResolvent
              T hP hInnerSymmetric hSelf hlambda z.1))) := by
    simpa only [standardOfRealLinearIsometry_apply] using
      ((standardOfRealLinearIsometry
        (H := P.VacuumOrthogonalHilbert)).continuous.tendsto _).comp hRe
  have hImOfReal :
      Tendsto
        (fun tau : G.AdmissibleRescaledDefectTime =>
          ofReal
            (G.admissibleRescaledDefectResolvent
              hInnerSymmetric tau hlambda z.2))
        G.admissibleRescaledDefectTimeFilter
        (𝓝
          (ofReal
            (G.vacuumOrthogonalContinuumRealResolvent
              T hP hInnerSymmetric hSelf hlambda z.2))) := by
    simpa only [standardOfRealLinearIsometry_apply] using
      ((standardOfRealLinearIsometry
        (H := P.VacuumOrthogonalHilbert)).continuous.tendsto _).comp hIm
  have hComplex := hReOfReal.add (hImOfReal.const_smul Complex.I)
  simpa only [diagonalComplexification_apply, ofReal, I_smul,
    neg_zero, add_zero, zero_add] using hComplex

/-- The actual continuum resolvent complexification lies in the closed diagonal
real-form star subalgebra, obtained from the pointwise strong limit of the
finite-time complexified resolvents. -/
theorem VacuumSemigroupGapSlope.vacuumOrthogonalContinuumDiagonalResolvent_mem_realForm
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ}
    (hlambda : lambda < G.mass / 2) :
    diagonalComplexification
        (G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf hlambda) ∈
      diagonalComplexificationStarSubalgebra
        (H := P.VacuumOrthogonalHilbert) := by
  let F : G.AdmissibleRescaledDefectTime →
      diagonalComplexificationStarSubalgebra
        (H := P.VacuumOrthogonalHilbert) :=
    fun tau =>
      diagonalComplexificationStarAlgEquiv
        (H := P.VacuumOrthogonalHilbert)
        (G.admissibleRescaledDefectResolvent
          hInnerSymmetric tau hlambda)
  apply
    mem_diagonalComplexificationStarSubalgebra_of_tendsto_apply
      (H := P.VacuumOrthogonalHilbert)
      (l := G.admissibleRescaledDefectTimeFilter)
      F
      (diagonalComplexification
        (G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf hlambda))
  intro z
  simpa [F] using
    G.admissibleRescaledDefectDiagonalComplexification_tendsto_continuumResolvent
      T hP hInnerSymmetric hSelf hlambda z

/-- The bounded real operator underlying the actual complex strong limit exists
uniquely.  Its target complex operator is the diagonal complexification of the
already-constructed continuum real resolvent. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectDiagonalComplexification_existsUnique_real_limit
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ}
    (hlambda : lambda < G.mass / 2) :
    ∃! R : P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert,
      diagonalComplexification R =
        diagonalComplexification
          (G.vacuumOrthogonalContinuumRealResolvent
            T hP hInnerSymmetric hSelf hlambda) := by
  apply
    tendsto_diagonalComplexification_apply_existsUnique_real_limit
      (H := P.VacuumOrthogonalHilbert)
      (l := G.admissibleRescaledDefectTimeFilter)
      (f := fun tau : G.AdmissibleRescaledDefectTime =>
        G.admissibleRescaledDefectResolvent
          hInnerSymmetric tau hlambda)
      (X := diagonalComplexification
        (G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf hlambda))
  intro z
  exact
    G.admissibleRescaledDefectDiagonalComplexification_tendsto_continuumResolvent
      T hP hInnerSymmetric hSelf hlambda z

/-- Any bounded real operator whose diagonal complexification is a pointwise
strong limit of the admissible finite-time complexified resolvents is exactly
the existing continuum real resolvent. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefect_real_limit_eq_continuumResolvent
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ}
    (hlambda : lambda < G.mass / 2)
    (R : P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert)
    (hR : ∀ z : StandardRealHilbertComplexification P.VacuumOrthogonalHilbert,
      Tendsto
        (fun tau : G.AdmissibleRescaledDefectTime =>
          diagonalComplexification
            (G.admissibleRescaledDefectResolvent
              hInnerSymmetric tau hlambda) z)
        G.admissibleRescaledDefectTimeFilter
        (𝓝 (diagonalComplexification R z))) :
    R = G.vacuumOrthogonalContinuumRealResolvent
      T hP hInnerSymmetric hSelf hlambda := by
  have hComplex :
      diagonalComplexification R =
        diagonalComplexification
          (G.vacuumOrthogonalContinuumRealResolvent
            T hP hInnerSymmetric hSelf hlambda) := by
    ext z
    exact tendsto_nhds_unique
      (hR z)
      (G.admissibleRescaledDefectDiagonalComplexification_tendsto_continuumResolvent
        T hP hInnerSymmetric hSelf hlambda z)
  apply
    (diagonalComplexificationLinearIsometry
      (H := P.VacuumOrthogonalHilbert)).injective
  simpa only [diagonalComplexificationLinearIsometry_apply] using hComplex

/-- Actual OS real-form strong-limit package: full-complexification pointwise
strong convergence, preservation of the diagonal real form, and the existing
canonical graph Kuratowski limits, without any operator-norm convergence
assumption. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectResolventRealFormStrongLimitPackage
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) :
    (∀ {lambda : ℝ} (hlambda : lambda < G.mass / 2),
      ∀ z : StandardRealHilbertComplexification P.VacuumOrthogonalHilbert,
        Tendsto
          (fun tau : G.AdmissibleRescaledDefectTime =>
            diagonalComplexification
              (G.admissibleRescaledDefectResolvent
                hInnerSymmetric tau hlambda) z)
          G.admissibleRescaledDefectTimeFilter
          (𝓝
            (diagonalComplexification
              (G.vacuumOrthogonalContinuumRealResolvent
                T hP hInnerSymmetric hSelf hlambda) z))) ∧
    (∀ {lambda : ℝ} (hlambda : lambda < G.mass / 2),
      diagonalComplexification
          (G.vacuumOrthogonalContinuumRealResolvent
            T hP hInnerSymmetric hSelf hlambda) ∈
        diagonalComplexificationStarSubalgebra
          (H := P.VacuumOrthogonalHilbert)) ∧
    (FilterSet.kuratowskiInnerLimit G.admissibleRescaledDefectTimeFilter
          (G.rescaledDefectGraphFamily T hInnerSymmetric
            (fun tau : G.AdmissibleRescaledDefectTime => tau)) =
        G.continuumHamiltonianGraph T hSelf ∧
      FilterSet.kuratowskiOuterLimit G.admissibleRescaledDefectTimeFilter
          (G.rescaledDefectGraphFamily T hInnerSymmetric
            (fun tau : G.AdmissibleRescaledDefectTime => tau)) =
        G.continuumHamiltonianGraph T hSelf) := by
  constructor
  · intro lambda hlambda z
    exact
      G.admissibleRescaledDefectDiagonalComplexification_tendsto_continuumResolvent
        T hP hInnerSymmetric hSelf hlambda z
  constructor
  · intro lambda hlambda
    exact
      G.vacuumOrthogonalContinuumDiagonalResolvent_mem_realForm
        T hP hInnerSymmetric hSelf hlambda
  · exact
      (G.canonicalRescaledDefectOperatorLimitPackage
        T hP hInnerSymmetric hSelf).2

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
