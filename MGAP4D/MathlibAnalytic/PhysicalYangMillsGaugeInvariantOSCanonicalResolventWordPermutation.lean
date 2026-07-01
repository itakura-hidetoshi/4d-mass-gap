import MGAP4D.MathlibAnalytic.ContinuousLinearMapOrderedProductPermutation
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalMixedResolventProductLimit
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalResolventIdentity

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

/-- At every admissible positive time, a finite mixed resolvent product depends
only on the permutation class of its below-half-mass shift list. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolvent_orderedProduct_eq_of_perm
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    {s t : List G.BelowHalfMassShift}
    (hPerm : s.Perm t) :
    ContinuousLinearMap.orderedProduct
        (fun sigma : G.BelowHalfMassShift =>
          G.admissibleRescaledDefectResolvent
            hInnerSymmetric tau sigma.property)
        s =
      ContinuousLinearMap.orderedProduct
        (fun sigma : G.BelowHalfMassShift =>
          G.admissibleRescaledDefectResolvent
            hInnerSymmetric tau sigma.property)
        t := by
  apply ContinuousLinearMap.orderedProduct_eq_of_perm_of_pairwise_comm
  · intro sigma rho
    exact
      G.admissibleRescaledDefectResolvent_comp_comm
        T hInnerSymmetric tau sigma.property rho.property
  · exact hPerm

/-- Pointwise finite-time form of permutation invariance. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolvent_orderedProduct_apply_eq_of_perm
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    {s t : List G.BelowHalfMassShift}
    (hPerm : s.Perm t)
    (y : P.VacuumOrthogonalHilbert) :
    ContinuousLinearMap.orderedProduct
        (fun sigma : G.BelowHalfMassShift =>
          G.admissibleRescaledDefectResolvent
            hInnerSymmetric tau sigma.property)
        s y =
      ContinuousLinearMap.orderedProduct
        (fun sigma : G.BelowHalfMassShift =>
          G.admissibleRescaledDefectResolvent
            hInnerSymmetric tau sigma.property)
        t y := by
  rw [
    G.admissibleRescaledDefectResolvent_orderedProduct_eq_of_perm
      T hInnerSymmetric tau hPerm]

/-- The continuum mixed resolvent product also depends only on the permutation
class of its below-half-mass shift list. -/
theorem VacuumSemigroupGapSlope.vacuumOrthogonalContinuumRealResolvent_orderedProduct_eq_of_perm
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {s t : List G.BelowHalfMassShift}
    (hPerm : s.Perm t) :
    ContinuousLinearMap.orderedProduct
        (fun sigma : G.BelowHalfMassShift =>
          G.vacuumOrthogonalContinuumRealResolvent
            T hP hInnerSymmetric hSelf sigma.property)
        s =
      ContinuousLinearMap.orderedProduct
        (fun sigma : G.BelowHalfMassShift =>
          G.vacuumOrthogonalContinuumRealResolvent
            T hP hInnerSymmetric hSelf sigma.property)
        t := by
  apply ContinuousLinearMap.orderedProduct_eq_of_perm_of_pairwise_comm
  · intro sigma rho
    exact
      G.vacuumOrthogonalContinuumRealResolvent_comp_comm
        T hP hInnerSymmetric hSelf sigma.property rho.property
  · exact hPerm

/-- Pointwise continuum form of permutation invariance. -/
theorem VacuumSemigroupGapSlope.vacuumOrthogonalContinuumRealResolvent_orderedProduct_apply_eq_of_perm
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {s t : List G.BelowHalfMassShift}
    (hPerm : s.Perm t)
    (y : P.VacuumOrthogonalHilbert) :
    ContinuousLinearMap.orderedProduct
        (fun sigma : G.BelowHalfMassShift =>
          G.vacuumOrthogonalContinuumRealResolvent
            T hP hInnerSymmetric hSelf sigma.property)
        s y =
      ContinuousLinearMap.orderedProduct
        (fun sigma : G.BelowHalfMassShift =>
          G.vacuumOrthogonalContinuumRealResolvent
            T hP hInnerSymmetric hSelf sigma.property)
        t y := by
  rw [
    G.vacuumOrthogonalContinuumRealResolvent_orderedProduct_eq_of_perm
      T hP hInnerSymmetric hSelf hPerm]

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
