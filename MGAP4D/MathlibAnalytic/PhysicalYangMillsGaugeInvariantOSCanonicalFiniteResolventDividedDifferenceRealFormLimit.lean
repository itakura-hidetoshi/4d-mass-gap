import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalFiniteResolventDividedDifference
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

/-- The finite-time bounded real operator given by the recursive divided
difference of a finite list of admissible rescaled-defect resolvents. -/
noncomputable def VacuumSemigroupGapSlope.admissibleRescaledDefectResolventFiniteDividedDifference
    {T : P.StronglyContinuousPhysicalSemigroup}
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    (shifts : List G.BelowHalfMassShift) :
    P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert :=
  ContinuousLinearMap.finiteResolventDividedDifference
    (fun sigma : G.BelowHalfMassShift => sigma.1)
    (fun sigma : G.BelowHalfMassShift =>
      G.admissibleRescaledDefectResolvent
        hInnerSymmetric tau sigma.property)
    shifts

/-- The corresponding continuum bounded real recursive resolvent divided
difference. -/
noncomputable def VacuumSemigroupGapSlope.continuumResolventFiniteDividedDifference
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (shifts : List G.BelowHalfMassShift) :
    P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert :=
  ContinuousLinearMap.finiteResolventDividedDifference
    (fun sigma : G.BelowHalfMassShift => sigma.1)
    (fun sigma : G.BelowHalfMassShift =>
      G.vacuumOrthogonalContinuumRealResolvent
        T hP hInnerSymmetric hSelf sigma.property)
    shifts

/-- Every finite parameter-distinct recursive resolvent divided difference
converges pointwise strongly after canonical diagonal complexification on the
full standard complexification. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventFiniteDividedDifferenceDiagonalComplexification_tendsto_continuum
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (shifts : List G.BelowHalfMassShift)
    (hPairwise : shifts.Pairwise fun sigma rho => sigma.1 ≠ rho.1)
    (z : StandardRealHilbertComplexification P.VacuumOrthogonalHilbert) :
    Tendsto
      (fun tau : G.AdmissibleRescaledDefectTime =>
        diagonalComplexification
          (G.admissibleRescaledDefectResolventFiniteDividedDifference
            hInnerSymmetric tau shifts) z)
      G.admissibleRescaledDefectTimeFilter
      (𝓝
        (diagonalComplexification
          (G.continuumResolventFiniteDividedDifference
            T hP hInnerSymmetric hSelf shifts) z)) := by
  have hRe :
      Tendsto
        (fun tau : G.AdmissibleRescaledDefectTime =>
          G.admissibleRescaledDefectResolventFiniteDividedDifference
            hInnerSymmetric tau shifts z.1)
        G.admissibleRescaledDefectTimeFilter
        (𝓝
          (G.continuumResolventFiniteDividedDifference
            T hP hInnerSymmetric hSelf shifts z.1)) := by
    simpa [
      VacuumSemigroupGapSlope.admissibleRescaledDefectResolventFiniteDividedDifference,
      VacuumSemigroupGapSlope.continuumResolventFiniteDividedDifference] using
      G.admissibleRescaledDefectResolvent_finiteDividedDifference_tendsto_continuumFiniteDividedDifference
        T hP hInnerSymmetric hSelf shifts hPairwise z.1
  have hIm :
      Tendsto
        (fun tau : G.AdmissibleRescaledDefectTime =>
          G.admissibleRescaledDefectResolventFiniteDividedDifference
            hInnerSymmetric tau shifts z.2)
        G.admissibleRescaledDefectTimeFilter
        (𝓝
          (G.continuumResolventFiniteDividedDifference
            T hP hInnerSymmetric hSelf shifts z.2)) := by
    simpa [
      VacuumSemigroupGapSlope.admissibleRescaledDefectResolventFiniteDividedDifference,
      VacuumSemigroupGapSlope.continuumResolventFiniteDividedDifference] using
      G.admissibleRescaledDefectResolvent_finiteDividedDifference_tendsto_continuumFiniteDividedDifference
        T hP hInnerSymmetric hSelf shifts hPairwise z.2
  have hReOfReal :
      Tendsto
        (fun tau : G.AdmissibleRescaledDefectTime =>
          ofReal
            (G.admissibleRescaledDefectResolventFiniteDividedDifference
              hInnerSymmetric tau shifts z.1))
        G.admissibleRescaledDefectTimeFilter
        (𝓝
          (ofReal
            (G.continuumResolventFiniteDividedDifference
              T hP hInnerSymmetric hSelf shifts z.1))) := by
    simpa only [standardOfRealLinearIsometry_apply] using
      ((standardOfRealLinearIsometry
        (H := P.VacuumOrthogonalHilbert)).continuous.tendsto _).comp hRe
  have hImOfReal :
      Tendsto
        (fun tau : G.AdmissibleRescaledDefectTime =>
          ofReal
            (G.admissibleRescaledDefectResolventFiniteDividedDifference
              hInnerSymmetric tau shifts z.2))
        G.admissibleRescaledDefectTimeFilter
        (𝓝
          (ofReal
            (G.continuumResolventFiniteDividedDifference
              T hP hInnerSymmetric hSelf shifts z.2))) := by
    simpa only [standardOfRealLinearIsometry_apply] using
      ((standardOfRealLinearIsometry
        (H := P.VacuumOrthogonalHilbert)).continuous.tendsto _).comp hIm
  have hComplex := hReOfReal.add (hImOfReal.const_smul Complex.I)
  have hSource :
      (fun tau : G.AdmissibleRescaledDefectTime =>
        diagonalComplexification
          (G.admissibleRescaledDefectResolventFiniteDividedDifference
            hInnerSymmetric tau shifts) z) =
      (fun tau : G.AdmissibleRescaledDefectTime =>
        ofReal
            (G.admissibleRescaledDefectResolventFiniteDividedDifference
              hInnerSymmetric tau shifts z.1) +
          Complex.I • ofReal
            (G.admissibleRescaledDefectResolventFiniteDividedDifference
              hInnerSymmetric tau shifts z.2)) := by
    funext tau
    rw [diagonalComplexification_apply]
    exact decompose _
  have hTarget :
      diagonalComplexification
          (G.continuumResolventFiniteDividedDifference
            T hP hInnerSymmetric hSelf shifts) z =
        ofReal
            (G.continuumResolventFiniteDividedDifference
              T hP hInnerSymmetric hSelf shifts z.1) +
          Complex.I • ofReal
            (G.continuumResolventFiniteDividedDifference
              T hP hInnerSymmetric hSelf shifts z.2) := by
    rw [diagonalComplexification_apply]
    exact decompose _
  rw [hSource, hTarget]
  exact hComplex

/-- The continuum recursive divided difference remains in the closed diagonal
real-form star subalgebra. -/
theorem VacuumSemigroupGapSlope.continuumResolventFiniteDividedDifferenceDiagonalComplexification_mem_realForm
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (shifts : List G.BelowHalfMassShift)
    (hPairwise : shifts.Pairwise fun sigma rho => sigma.1 ≠ rho.1) :
    diagonalComplexification
        (G.continuumResolventFiniteDividedDifference
          T hP hInnerSymmetric hSelf shifts) ∈
      diagonalComplexificationStarSubalgebra
        (H := P.VacuumOrthogonalHilbert) := by
  let F : G.AdmissibleRescaledDefectTime →
      diagonalComplexificationStarSubalgebra
        (H := P.VacuumOrthogonalHilbert) :=
    fun tau =>
      diagonalComplexificationStarAlgEquiv
        (H := P.VacuumOrthogonalHilbert)
        (G.admissibleRescaledDefectResolventFiniteDividedDifference
          hInnerSymmetric tau shifts)
  apply
    mem_diagonalComplexificationStarSubalgebra_of_tendsto_apply
      (H := P.VacuumOrthogonalHilbert)
      (l := G.admissibleRescaledDefectTimeFilter)
      F
      (diagonalComplexification
        (G.continuumResolventFiniteDividedDifference
          T hP hInnerSymmetric hSelf shifts))
  intro z
  simpa [F] using
    G.admissibleRescaledDefectResolventFiniteDividedDifferenceDiagonalComplexification_tendsto_continuum
      T hP hInnerSymmetric hSelf shifts hPairwise z

/-- The bounded real operator underlying the complex strong limit of every
finite parameter-distinct recursive divided difference exists uniquely. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventFiniteDividedDifferenceDiagonalComplexification_existsUnique_real_limit
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (shifts : List G.BelowHalfMassShift)
    (hPairwise : shifts.Pairwise fun sigma rho => sigma.1 ≠ rho.1) :
    ∃! R : P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert,
      diagonalComplexification R =
        diagonalComplexification
          (G.continuumResolventFiniteDividedDifference
            T hP hInnerSymmetric hSelf shifts) := by
  apply
    tendsto_diagonalComplexification_apply_existsUnique_real_limit
      (H := P.VacuumOrthogonalHilbert)
      (l := G.admissibleRescaledDefectTimeFilter)
      (f := fun tau : G.AdmissibleRescaledDefectTime =>
        G.admissibleRescaledDefectResolventFiniteDividedDifference
          hInnerSymmetric tau shifts)
      (X := diagonalComplexification
        (G.continuumResolventFiniteDividedDifference
          T hP hInnerSymmetric hSelf shifts))
  intro z
  exact
    G.admissibleRescaledDefectResolventFiniteDividedDifferenceDiagonalComplexification_tendsto_continuum
      T hP hInnerSymmetric hSelf shifts hPairwise z

/-- Any real bounded operator producing the same complex pointwise strong limit
is exactly the continuum recursive divided difference. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventFiniteDividedDifference_real_limit_eq_continuum
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (shifts : List G.BelowHalfMassShift)
    (hPairwise : shifts.Pairwise fun sigma rho => sigma.1 ≠ rho.1)
    (R : P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert)
    (hR : ∀ z : StandardRealHilbertComplexification P.VacuumOrthogonalHilbert,
      Tendsto
        (fun tau : G.AdmissibleRescaledDefectTime =>
          diagonalComplexification
            (G.admissibleRescaledDefectResolventFiniteDividedDifference
              hInnerSymmetric tau shifts) z)
        G.admissibleRescaledDefectTimeFilter
        (𝓝 (diagonalComplexification R z))) :
    R = G.continuumResolventFiniteDividedDifference
      T hP hInnerSymmetric hSelf shifts := by
  have hComplex :
      diagonalComplexification R =
        diagonalComplexification
          (G.continuumResolventFiniteDividedDifference
            T hP hInnerSymmetric hSelf shifts) := by
    ext z
    exact tendsto_nhds_unique
      (hR z)
      (G.admissibleRescaledDefectResolventFiniteDividedDifferenceDiagonalComplexification_tendsto_continuum
        T hP hInnerSymmetric hSelf shifts hPairwise z)
  apply
    (diagonalComplexificationLinearIsometry
      (H := P.VacuumOrthogonalHilbert)).injective
  simpa only [diagonalComplexificationLinearIsometry_apply] using hComplex

/-- Actual OS real-form strong-limit package for arbitrary finite
parameter-distinct recursive resolvent divided differences. -/
theorem VacuumSemigroupGapSlope.canonicalFiniteResolventDividedDifferenceRealFormStrongLimitPackage
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (shifts : List G.BelowHalfMassShift)
    (hPairwise : shifts.Pairwise fun sigma rho => sigma.1 ≠ rho.1) :
    (∀ z : StandardRealHilbertComplexification P.VacuumOrthogonalHilbert,
      Tendsto
        (fun tau : G.AdmissibleRescaledDefectTime =>
          diagonalComplexification
            (G.admissibleRescaledDefectResolventFiniteDividedDifference
              hInnerSymmetric tau shifts) z)
        G.admissibleRescaledDefectTimeFilter
        (𝓝
          (diagonalComplexification
            (G.continuumResolventFiniteDividedDifference
              T hP hInnerSymmetric hSelf shifts) z))) ∧
    diagonalComplexification
        (G.continuumResolventFiniteDividedDifference
          T hP hInnerSymmetric hSelf shifts) ∈
      diagonalComplexificationStarSubalgebra
        (H := P.VacuumOrthogonalHilbert) ∧
    ∃! R : P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert,
      diagonalComplexification R =
        diagonalComplexification
          (G.continuumResolventFiniteDividedDifference
            T hP hInnerSymmetric hSelf shifts) := by
  constructor
  · intro z
    exact
      G.admissibleRescaledDefectResolventFiniteDividedDifferenceDiagonalComplexification_tendsto_continuum
        T hP hInnerSymmetric hSelf shifts hPairwise z
  constructor
  · exact
      G.continuumResolventFiniteDividedDifferenceDiagonalComplexification_mem_realForm
        T hP hInnerSymmetric hSelf shifts hPairwise
  · exact
      G.admissibleRescaledDefectResolventFiniteDividedDifferenceDiagonalComplexification_existsUnique_real_limit
        T hP hInnerSymmetric hSelf shifts hPairwise

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
