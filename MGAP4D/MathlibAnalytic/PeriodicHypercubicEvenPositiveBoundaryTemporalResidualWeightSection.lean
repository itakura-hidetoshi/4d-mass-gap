import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPositiveBoundaryTemporalResidualOpenPathSection
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPositiveBoundaryTemporalWilsonResidualProduct
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- On the canonical four-companion open-half section, the entire literal
positive-boundary temporal residual Wilson interaction is independent of the
four selected companion variables.  It is retained exactly as the product of
its boundary relative kernels against the identity open path.

Thus no residual plaquette is deleted and no residual interaction is replaced
by `1`; only its open-half dependence is trivialized by the exact residual-path
geometry. -/
theorem
    periodicHypercubicEvenPositiveBoundaryTemporalWilsonResidualWeight_fourCompanionSection_eq_boundaryProduct
    (H : ℕ)
    (hH : 1 < H)
    (beta : ℝ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (u : Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    periodicHypercubicEvenPositiveBoundaryTemporalWilsonResidualWeight H beta
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
          b
          (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfSection
            H (Nat.zero_lt_of_lt hH) u)
          y) =
      ∏ p ∈ periodicHypercubicEvenPositiveBoundaryTemporalResidualPlaquettes H,
        specialUnitaryWilsonRelativeKernel 2 beta
          (periodicHypercubicEvenPositiveBoundaryTemporalFiberedBoundaryLeg b p)
          1 := by
  rw [
    periodicHypercubicEvenPositiveBoundaryTemporalWilsonResidualWeight_boundaryFibered_eq_relativeKernelProduct
      (Nat.zero_lt_of_lt hH) beta b
      (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfSection
        H (Nat.zero_lt_of_lt hH) u) y]
  apply Finset.prod_congr rfl
  intro p hp
  rw [
    periodicHypercubicEvenPositiveBoundaryTemporalResidualFiberedOpenPath_fourCompanionSection_eq_one
      H 2 hH u p hp]

/-- Consequently, the exact residual Wilson weight is unchanged when the four
selected companion open-half values are varied.  The residual interaction is
still present on the boundary carrier; only the selected four-dimensional
open-half coordinate is separated from it. -/
theorem
    periodicHypercubicEvenPositiveBoundaryTemporalWilsonResidualWeight_fourCompanionSection_independent
    (H : ℕ)
    (hH : 1 < H)
    (beta : ℝ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (u v : Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (y z : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    periodicHypercubicEvenPositiveBoundaryTemporalWilsonResidualWeight H beta
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
          b
          (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfSection
            H (Nat.zero_lt_of_lt hH) u)
          y) =
      periodicHypercubicEvenPositiveBoundaryTemporalWilsonResidualWeight H beta
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
          b
          (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfSection
            H (Nat.zero_lt_of_lt hH) v)
          z) := by
  rw [
    periodicHypercubicEvenPositiveBoundaryTemporalWilsonResidualWeight_fourCompanionSection_eq_boundaryProduct
      H hH beta b u y,
    periodicHypercubicEvenPositiveBoundaryTemporalWilsonResidualWeight_fourCompanionSection_eq_boundaryProduct
      H hH beta b v z]

end

end MathlibAnalytic
end MGAP4D
