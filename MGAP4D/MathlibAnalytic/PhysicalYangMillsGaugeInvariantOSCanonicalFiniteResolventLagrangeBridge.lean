import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteResolventLagrangeBridge
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalFiniteResolventDividedDifference

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace LinearPMap

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- At every admissible positive time, the closed finite Lagrange normal form
of a parameter-distinct shift list equals its ordered resolvent product. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolvent_finiteLagrangeNormalForm_eq_orderedProduct
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    (shifts : List G.BelowHalfMassShift)
    (hPairwise : shifts.Pairwise fun sigma rho => sigma.1 ≠ rho.1) :
    ContinuousLinearMap.finiteResolventLagrangeNormalForm
        (fun sigma : G.BelowHalfMassShift => sigma.1)
        (fun sigma : G.BelowHalfMassShift =>
          G.admissibleRescaledDefectResolvent
            hInnerSymmetric tau sigma.property)
        shifts =
      ContinuousLinearMap.orderedProduct
        (fun sigma : G.BelowHalfMassShift =>
          G.admissibleRescaledDefectResolvent
            hInnerSymmetric tau sigma.property)
        shifts := by
  calc
    ContinuousLinearMap.finiteResolventLagrangeNormalForm
        (fun sigma : G.BelowHalfMassShift => sigma.1)
        (fun sigma : G.BelowHalfMassShift =>
          G.admissibleRescaledDefectResolvent
            hInnerSymmetric tau sigma.property)
        shifts =
      ContinuousLinearMap.finiteResolventDividedDifference
        (fun sigma : G.BelowHalfMassShift => sigma.1)
        (fun sigma : G.BelowHalfMassShift =>
          G.admissibleRescaledDefectResolvent
            hInnerSymmetric tau sigma.property)
        shifts :=
      (ContinuousLinearMap.finiteResolventDividedDifference_eq_finiteResolventLagrangeNormalForm_of_pairwise
        (fun sigma : G.BelowHalfMassShift => sigma.1)
        (fun sigma : G.BelowHalfMassShift =>
          G.admissibleRescaledDefectResolvent
            hInnerSymmetric tau sigma.property)
        shifts hPairwise).symm
    _ = ContinuousLinearMap.orderedProduct
        (fun sigma : G.BelowHalfMassShift =>
          G.admissibleRescaledDefectResolvent
            hInnerSymmetric tau sigma.property)
        shifts :=
      G.admissibleRescaledDefectResolvent_finiteDividedDifference_eq_orderedProduct
        T hInnerSymmetric tau shifts hPairwise

/-- The closed finite Lagrange normal form of a parameter-distinct continuum
shift list equals its ordered excitation-Hamiltonian resolvent product. -/
theorem VacuumSemigroupGapSlope.vacuumOrthogonalContinuumRealResolvent_finiteLagrangeNormalForm_eq_orderedProduct
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (shifts : List G.BelowHalfMassShift)
    (hPairwise : shifts.Pairwise fun sigma rho => sigma.1 ≠ rho.1) :
    ContinuousLinearMap.finiteResolventLagrangeNormalForm
        (fun sigma : G.BelowHalfMassShift => sigma.1)
        (fun sigma : G.BelowHalfMassShift =>
          G.vacuumOrthogonalContinuumRealResolvent
            T hP hInnerSymmetric hSelf sigma.property)
        shifts =
      ContinuousLinearMap.orderedProduct
        (fun sigma : G.BelowHalfMassShift =>
          G.vacuumOrthogonalContinuumRealResolvent
            T hP hInnerSymmetric hSelf sigma.property)
        shifts := by
  calc
    ContinuousLinearMap.finiteResolventLagrangeNormalForm
        (fun sigma : G.BelowHalfMassShift => sigma.1)
        (fun sigma : G.BelowHalfMassShift =>
          G.vacuumOrthogonalContinuumRealResolvent
            T hP hInnerSymmetric hSelf sigma.property)
        shifts =
      ContinuousLinearMap.finiteResolventDividedDifference
        (fun sigma : G.BelowHalfMassShift => sigma.1)
        (fun sigma : G.BelowHalfMassShift =>
          G.vacuumOrthogonalContinuumRealResolvent
            T hP hInnerSymmetric hSelf sigma.property)
        shifts :=
      (ContinuousLinearMap.finiteResolventDividedDifference_eq_finiteResolventLagrangeNormalForm_of_pairwise
        (fun sigma : G.BelowHalfMassShift => sigma.1)
        (fun sigma : G.BelowHalfMassShift =>
          G.vacuumOrthogonalContinuumRealResolvent
            T hP hInnerSymmetric hSelf sigma.property)
        shifts hPairwise).symm
    _ = ContinuousLinearMap.orderedProduct
        (fun sigma : G.BelowHalfMassShift =>
          G.vacuumOrthogonalContinuumRealResolvent
            T hP hInnerSymmetric hSelf sigma.property)
        shifts :=
      G.vacuumOrthogonalContinuumRealResolvent_finiteDividedDifference_eq_orderedProduct
        T hP hInnerSymmetric hSelf shifts hPairwise

/-- Closed finite Lagrange normal forms of parameter-distinct finite-time
resolvent lists converge strongly to the continuum Lagrange normal form. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolvent_finiteLagrangeNormalForm_tendsto_continuumFiniteLagrangeNormalForm
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (shifts : List G.BelowHalfMassShift)
    (hPairwise : shifts.Pairwise fun sigma rho => sigma.1 ≠ rho.1)
    (y : P.VacuumOrthogonalHilbert) :
    Tendsto
      (fun tau : G.AdmissibleRescaledDefectTime =>
        ContinuousLinearMap.finiteResolventLagrangeNormalForm
          (fun sigma : G.BelowHalfMassShift => sigma.1)
          (fun sigma : G.BelowHalfMassShift =>
            G.admissibleRescaledDefectResolvent
              hInnerSymmetric tau sigma.property)
          shifts y)
      G.admissibleRescaledDefectTimeFilter
      (𝓝
        (ContinuousLinearMap.finiteResolventLagrangeNormalForm
          (fun sigma : G.BelowHalfMassShift => sigma.1)
          (fun sigma : G.BelowHalfMassShift =>
            G.vacuumOrthogonalContinuumRealResolvent
              T hP hInnerSymmetric hSelf sigma.property)
          shifts y)) := by
  have hProduct :=
    G.admissibleRescaledDefectResolvent_orderedProduct_tendsto_continuumResolvent_orderedProduct
      T hP hInnerSymmetric hSelf shifts y
  have hFinite : ∀ tau : G.AdmissibleRescaledDefectTime,
      ContinuousLinearMap.finiteResolventLagrangeNormalForm
          (fun sigma : G.BelowHalfMassShift => sigma.1)
          (fun sigma : G.BelowHalfMassShift =>
            G.admissibleRescaledDefectResolvent
              hInnerSymmetric tau sigma.property)
          shifts =
        ContinuousLinearMap.orderedProduct
          (fun sigma : G.BelowHalfMassShift =>
            G.admissibleRescaledDefectResolvent
              hInnerSymmetric tau sigma.property)
          shifts := by
    intro tau
    exact
      G.admissibleRescaledDefectResolvent_finiteLagrangeNormalForm_eq_orderedProduct
        T hInnerSymmetric tau shifts hPairwise
  have hContinuum :
      ContinuousLinearMap.finiteResolventLagrangeNormalForm
          (fun sigma : G.BelowHalfMassShift => sigma.1)
          (fun sigma : G.BelowHalfMassShift =>
            G.vacuumOrthogonalContinuumRealResolvent
              T hP hInnerSymmetric hSelf sigma.property)
          shifts =
        ContinuousLinearMap.orderedProduct
          (fun sigma : G.BelowHalfMassShift =>
            G.vacuumOrthogonalContinuumRealResolvent
              T hP hInnerSymmetric hSelf sigma.property)
          shifts :=
    G.vacuumOrthogonalContinuumRealResolvent_finiteLagrangeNormalForm_eq_orderedProduct
      T hP hInnerSymmetric hSelf shifts hPairwise
  have hFunction :
      (fun tau : G.AdmissibleRescaledDefectTime =>
        ContinuousLinearMap.finiteResolventLagrangeNormalForm
          (fun sigma : G.BelowHalfMassShift => sigma.1)
          (fun sigma : G.BelowHalfMassShift =>
            G.admissibleRescaledDefectResolvent
              hInnerSymmetric tau sigma.property)
          shifts y) =
      (fun tau : G.AdmissibleRescaledDefectTime =>
        ContinuousLinearMap.orderedProduct
          (fun sigma : G.BelowHalfMassShift =>
            G.admissibleRescaledDefectResolvent
              hInnerSymmetric tau sigma.property)
          shifts y) := by
    funext tau
    rw [hFinite tau]
  rw [hFunction, hContinuum]
  exact hProduct

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
