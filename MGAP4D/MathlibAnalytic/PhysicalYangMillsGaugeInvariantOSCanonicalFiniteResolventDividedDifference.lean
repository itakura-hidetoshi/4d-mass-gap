import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteResolventDividedDifference
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalResolventIdentity
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalMixedResolventProductLimit

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

/-- At every admissible positive time, the recursive divided difference of a
finite parameter-distinct shift list is its ordered resolvent product. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolvent_finiteDividedDifference_eq_orderedProduct
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    (shifts : List G.BelowHalfMassShift)
    (hPairwise : shifts.Pairwise fun sigma rho => sigma.1 ≠ rho.1) :
    ContinuousLinearMap.finiteResolventDividedDifference
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
  apply
    ContinuousLinearMap.finiteResolventDividedDifference_eq_orderedProduct_of_pairwise
      (parameter := fun sigma : G.BelowHalfMassShift => sigma.1)
      (A := fun sigma : G.BelowHalfMassShift =>
        G.admissibleRescaledDefectResolvent
          hInnerSymmetric tau sigma.property)
  · intro sigma rho hne
    exact
      G.admissibleRescaledDefectResolvent_identity
        T hInnerSymmetric tau sigma.property rho.property
  · exact hPairwise

/-- The recursive divided difference of a finite parameter-distinct shift list
is also the ordered continuum Hamiltonian-resolvent product. -/
theorem VacuumSemigroupGapSlope.vacuumOrthogonalContinuumRealResolvent_finiteDividedDifference_eq_orderedProduct
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (shifts : List G.BelowHalfMassShift)
    (hPairwise : shifts.Pairwise fun sigma rho => sigma.1 ≠ rho.1) :
    ContinuousLinearMap.finiteResolventDividedDifference
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
  apply
    ContinuousLinearMap.finiteResolventDividedDifference_eq_orderedProduct_of_pairwise
      (parameter := fun sigma : G.BelowHalfMassShift => sigma.1)
      (A := fun sigma : G.BelowHalfMassShift =>
        G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf sigma.property)
  · intro sigma rho hne
    exact
      G.vacuumOrthogonalContinuumRealResolvent_identity
        T hP hInnerSymmetric hSelf sigma.property rho.property
  · exact hPairwise

/-- Finite recursive resolvent divided differences converge strongly from the
admissible rescaled defects to the continuum Hamiltonian divided difference. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolvent_finiteDividedDifference_tendsto_continuumFiniteDividedDifference
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
        ContinuousLinearMap.finiteResolventDividedDifference
          (fun sigma : G.BelowHalfMassShift => sigma.1)
          (fun sigma : G.BelowHalfMassShift =>
            G.admissibleRescaledDefectResolvent
              hInnerSymmetric tau sigma.property)
          shifts y)
      G.admissibleRescaledDefectTimeFilter
      (𝓝
        (ContinuousLinearMap.finiteResolventDividedDifference
          (fun sigma : G.BelowHalfMassShift => sigma.1)
          (fun sigma : G.BelowHalfMassShift =>
            G.vacuumOrthogonalContinuumRealResolvent
              T hP hInnerSymmetric hSelf sigma.property)
          shifts y)) := by
  have hProduct :=
    G.admissibleRescaledDefectResolvent_orderedProduct_tendsto_continuumResolvent_orderedProduct
      T hP hInnerSymmetric hSelf shifts y
  have hFinite : ∀ tau : G.AdmissibleRescaledDefectTime,
      ContinuousLinearMap.finiteResolventDividedDifference
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
      G.admissibleRescaledDefectResolvent_finiteDividedDifference_eq_orderedProduct
        T hInnerSymmetric tau shifts hPairwise
  have hContinuum :
      ContinuousLinearMap.finiteResolventDividedDifference
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
    G.vacuumOrthogonalContinuumRealResolvent_finiteDividedDifference_eq_orderedProduct
      T hP hInnerSymmetric hSelf shifts hPairwise
  have hFunction :
      (fun tau : G.AdmissibleRescaledDefectTime =>
        ContinuousLinearMap.finiteResolventDividedDifference
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
