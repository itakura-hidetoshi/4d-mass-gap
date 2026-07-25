import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalFiniteResolventLagrangeBridge
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalFiniteResolventDividedDifferenceRealFormLimit

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

local instance belowHalfMassShiftDecidableEq
    {T : P.StronglyContinuousPhysicalSemigroup}
    (G : T.VacuumSemigroupGapSlope) :
    DecidableEq G.BelowHalfMassShift :=
  Classical.decEq _

/-- The finite-time bounded real operator given by the closed barycentric
Lagrange normal form of a finite list of admissible rescaled-defect resolvents. -/
noncomputable def VacuumSemigroupGapSlope.admissibleRescaledDefectResolventFiniteLagrangeNormalForm
    {T : P.StronglyContinuousPhysicalSemigroup}
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    (shifts : List G.BelowHalfMassShift) :
    P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert :=
  ContinuousLinearMap.finiteResolventLagrangeNormalForm
    (fun sigma : G.BelowHalfMassShift => sigma.1)
    (fun sigma : G.BelowHalfMassShift =>
      G.admissibleRescaledDefectResolvent
        hInnerSymmetric tau sigma.property)
    shifts

/-- The corresponding continuum bounded real closed barycentric Lagrange
normal form. -/
noncomputable def VacuumSemigroupGapSlope.continuumResolventFiniteLagrangeNormalForm
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (shifts : List G.BelowHalfMassShift) :
    P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert :=
  ContinuousLinearMap.finiteResolventLagrangeNormalForm
    (fun sigma : G.BelowHalfMassShift => sigma.1)
    (fun sigma : G.BelowHalfMassShift =>
      G.vacuumOrthogonalContinuumRealResolvent
        T hP hInnerSymmetric hSelf sigma.property)
    shifts

/-- For pairwise-distinct shifts, the finite-time closed Lagrange operator is
exactly the previously bundled recursive divided-difference operator. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventFiniteLagrangeNormalForm_eq_finiteDividedDifference
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    (shifts : List G.BelowHalfMassShift)
    (hPairwise : shifts.Pairwise fun sigma rho => sigma.1 ≠ rho.1) :
    G.admissibleRescaledDefectResolventFiniteLagrangeNormalForm
        hInnerSymmetric tau shifts =
      G.admissibleRescaledDefectResolventFiniteDividedDifference
        hInnerSymmetric tau shifts := by
  simpa [
    VacuumSemigroupGapSlope.admissibleRescaledDefectResolventFiniteLagrangeNormalForm,
    VacuumSemigroupGapSlope.admissibleRescaledDefectResolventFiniteDividedDifference] using
    (ContinuousLinearMap.finiteResolventDividedDifference_eq_finiteResolventLagrangeNormalForm_of_pairwise
      (fun sigma : G.BelowHalfMassShift => sigma.1)
      (fun sigma : G.BelowHalfMassShift =>
        G.admissibleRescaledDefectResolvent
          hInnerSymmetric tau sigma.property)
      shifts hPairwise).symm

/-- For pairwise-distinct shifts, the continuum closed Lagrange operator is
exactly the previously bundled continuum recursive divided difference. -/
theorem VacuumSemigroupGapSlope.continuumResolventFiniteLagrangeNormalForm_eq_finiteDividedDifference
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (shifts : List G.BelowHalfMassShift)
    (hPairwise : shifts.Pairwise fun sigma rho => sigma.1 ≠ rho.1) :
    G.continuumResolventFiniteLagrangeNormalForm
        T hP hInnerSymmetric hSelf shifts =
      G.continuumResolventFiniteDividedDifference
        T hP hInnerSymmetric hSelf shifts := by
  simpa [
    VacuumSemigroupGapSlope.continuumResolventFiniteLagrangeNormalForm,
    VacuumSemigroupGapSlope.continuumResolventFiniteDividedDifference] using
    (ContinuousLinearMap.finiteResolventDividedDifference_eq_finiteResolventLagrangeNormalForm_of_pairwise
      (fun sigma : G.BelowHalfMassShift => sigma.1)
      (fun sigma : G.BelowHalfMassShift =>
        G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf sigma.property)
      shifts hPairwise).symm

/-- Every finite parameter-distinct closed Lagrange resolvent normal form
converges pointwise strongly after canonical diagonal complexification on the
full standard complexification. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventFiniteLagrangeNormalFormDiagonalComplexification_tendsto_continuum
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
          (G.admissibleRescaledDefectResolventFiniteLagrangeNormalForm
            hInnerSymmetric tau shifts) z)
      G.admissibleRescaledDefectTimeFilter
      (𝓝
        (diagonalComplexification
          (G.continuumResolventFiniteLagrangeNormalForm
            T hP hInnerSymmetric hSelf shifts) z)) := by
  have hSource :
      (fun tau : G.AdmissibleRescaledDefectTime =>
        diagonalComplexification
          (G.admissibleRescaledDefectResolventFiniteLagrangeNormalForm
            hInnerSymmetric tau shifts) z) =
      (fun tau : G.AdmissibleRescaledDefectTime =>
        diagonalComplexification
          (G.admissibleRescaledDefectResolventFiniteDividedDifference
            hInnerSymmetric tau shifts) z) := by
    funext tau
    rw [G.admissibleRescaledDefectResolventFiniteLagrangeNormalForm_eq_finiteDividedDifference
      T hInnerSymmetric tau shifts hPairwise]
  have hTarget :
      diagonalComplexification
          (G.continuumResolventFiniteLagrangeNormalForm
            T hP hInnerSymmetric hSelf shifts) z =
        diagonalComplexification
          (G.continuumResolventFiniteDividedDifference
            T hP hInnerSymmetric hSelf shifts) z := by
    rw [G.continuumResolventFiniteLagrangeNormalForm_eq_finiteDividedDifference
      T hP hInnerSymmetric hSelf shifts hPairwise]
  rw [hSource, hTarget]
  exact
    G.admissibleRescaledDefectResolventFiniteDividedDifferenceDiagonalComplexification_tendsto_continuum
      T hP hInnerSymmetric hSelf shifts hPairwise z

/-- The continuum closed Lagrange normal form remains in the closed diagonal
real-form star subalgebra. -/
theorem VacuumSemigroupGapSlope.continuumResolventFiniteLagrangeNormalFormDiagonalComplexification_mem_realForm
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (shifts : List G.BelowHalfMassShift)
    (hPairwise : shifts.Pairwise fun sigma rho => sigma.1 ≠ rho.1) :
    diagonalComplexification
        (G.continuumResolventFiniteLagrangeNormalForm
          T hP hInnerSymmetric hSelf shifts) ∈
      diagonalComplexificationStarSubalgebra
        (H := P.VacuumOrthogonalHilbert) := by
  rw [G.continuumResolventFiniteLagrangeNormalForm_eq_finiteDividedDifference
    T hP hInnerSymmetric hSelf shifts hPairwise]
  exact
    G.continuumResolventFiniteDividedDifferenceDiagonalComplexification_mem_realForm
      T hP hInnerSymmetric hSelf shifts hPairwise

/-- The bounded real operator underlying the complex strong limit of every
finite parameter-distinct closed Lagrange normal form exists uniquely. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventFiniteLagrangeNormalFormDiagonalComplexification_existsUnique_real_limit
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
          (G.continuumResolventFiniteLagrangeNormalForm
            T hP hInnerSymmetric hSelf shifts) := by
  rw [G.continuumResolventFiniteLagrangeNormalForm_eq_finiteDividedDifference
    T hP hInnerSymmetric hSelf shifts hPairwise]
  exact
    G.admissibleRescaledDefectResolventFiniteDividedDifferenceDiagonalComplexification_existsUnique_real_limit
      T hP hInnerSymmetric hSelf shifts hPairwise

/-- Any real bounded operator producing the same complex pointwise strong limit
is exactly the continuum closed Lagrange normal form. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventFiniteLagrangeNormalForm_real_limit_eq_continuum
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
            (G.admissibleRescaledDefectResolventFiniteLagrangeNormalForm
              hInnerSymmetric tau shifts) z)
        G.admissibleRescaledDefectTimeFilter
        (𝓝 (diagonalComplexification R z))) :
    R = G.continuumResolventFiniteLagrangeNormalForm
      T hP hInnerSymmetric hSelf shifts := by
  have hRDivided : ∀ z : StandardRealHilbertComplexification P.VacuumOrthogonalHilbert,
      Tendsto
        (fun tau : G.AdmissibleRescaledDefectTime =>
          diagonalComplexification
            (G.admissibleRescaledDefectResolventFiniteDividedDifference
              hInnerSymmetric tau shifts) z)
        G.admissibleRescaledDefectTimeFilter
        (𝓝 (diagonalComplexification R z)) := by
    intro z
    have hSource :
        (fun tau : G.AdmissibleRescaledDefectTime =>
          diagonalComplexification
            (G.admissibleRescaledDefectResolventFiniteLagrangeNormalForm
              hInnerSymmetric tau shifts) z) =
        (fun tau : G.AdmissibleRescaledDefectTime =>
          diagonalComplexification
            (G.admissibleRescaledDefectResolventFiniteDividedDifference
              hInnerSymmetric tau shifts) z) := by
      funext tau
      rw [G.admissibleRescaledDefectResolventFiniteLagrangeNormalForm_eq_finiteDividedDifference
        T hInnerSymmetric tau shifts hPairwise]
    rw [← hSource]
    exact hR z
  calc
    R = G.continuumResolventFiniteDividedDifference
        T hP hInnerSymmetric hSelf shifts :=
      G.admissibleRescaledDefectResolventFiniteDividedDifference_real_limit_eq_continuum
        T hP hInnerSymmetric hSelf shifts hPairwise R hRDivided
    _ = G.continuumResolventFiniteLagrangeNormalForm
        T hP hInnerSymmetric hSelf shifts :=
      (G.continuumResolventFiniteLagrangeNormalForm_eq_finiteDividedDifference
        T hP hInnerSymmetric hSelf shifts hPairwise).symm

/-- Actual OS real-form strong-limit package for arbitrary finite
parameter-distinct closed Lagrange resolvent normal forms. -/
theorem VacuumSemigroupGapSlope.canonicalFiniteResolventLagrangeRealFormStrongLimitPackage
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
            (G.admissibleRescaledDefectResolventFiniteLagrangeNormalForm
              hInnerSymmetric tau shifts) z)
        G.admissibleRescaledDefectTimeFilter
        (𝓝
          (diagonalComplexification
            (G.continuumResolventFiniteLagrangeNormalForm
              T hP hInnerSymmetric hSelf shifts) z))) ∧
    diagonalComplexification
        (G.continuumResolventFiniteLagrangeNormalForm
          T hP hInnerSymmetric hSelf shifts) ∈
      diagonalComplexificationStarSubalgebra
        (H := P.VacuumOrthogonalHilbert) ∧
    ∃! R : P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert,
      diagonalComplexification R =
        diagonalComplexification
          (G.continuumResolventFiniteLagrangeNormalForm
            T hP hInnerSymmetric hSelf shifts) := by
  constructor
  · intro z
    exact
      G.admissibleRescaledDefectResolventFiniteLagrangeNormalFormDiagonalComplexification_tendsto_continuum
        T hP hInnerSymmetric hSelf shifts hPairwise z
  constructor
  · exact
      G.continuumResolventFiniteLagrangeNormalFormDiagonalComplexification_mem_realForm
        T hP hInnerSymmetric hSelf shifts hPairwise
  · exact
      G.admissibleRescaledDefectResolventFiniteLagrangeNormalFormDiagonalComplexification_existsUnique_real_limit
        T hP hInnerSymmetric hSelf shifts hPairwise

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
