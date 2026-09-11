import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPositiveBoundaryTemporalResidualWeightSection
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCyclicFourEdgeWilsonPartialFock
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance positiveBoundaryTemporalWilsonSectionFactorizationSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

/-- The canonical four-companion section is an exact right inverse of the
physical four-edge open-path word.  Thus the four selected open-path variables
are genuinely independent `SU(2)` coordinates, not merely abstract probes. -/
@[simp] theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfFourEdgeWord_fourCompanionSection
    (H : ℕ)
    (hH : 0 < H)
    (u : Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfFourEdgeWord H
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfSection
          H hH u) =
      u := by
  funext k
  exact
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenPath_section
      H 2 hH u k

/-- On the exact four-companion section, the selected four-plaquette Wilson
weight is literally the product of four independent relative Wilson kernels
between the physical boundary edges and the prescribed `SU(2)` values. -/
theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionWilsonWeight_fourCompanionSection_eq_relativeKernelProduct
    (H : ℕ)
    (hH : 0 < H)
    (beta : ℝ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (u : Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionWilsonWeight H beta
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
          b
          (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfSection
            H hH u)
          y) =
      (specialUnitaryWilsonRelativeKernel 2 beta
          (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b 2) (u 2) *
        specialUnitaryWilsonRelativeKernel 2 beta
          (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b 3) (u 3)) *
      (specialUnitaryWilsonRelativeKernel 2 beta
          (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b 0) (u 0) *
        specialUnitaryWilsonRelativeKernel 2 beta
          (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b 1) (u 1)) := by
  rw [periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionWilsonWeight_eq_product]
  unfold periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionWilsonProductOnConfiguration
  rw [
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionWilsonBoltzmannCentralFunction_eq_relativeKernel
      hH beta b
      (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfSection H hH u) y 2,
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionWilsonBoltzmannCentralFunction_eq_relativeKernel
      hH beta b
      (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfSection H hH u) y 3,
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionWilsonBoltzmannCentralFunction_eq_relativeKernel
      hH beta b
      (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfSection H hH u) y 0,
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionWilsonBoltzmannCentralFunction_eq_relativeKernel
      hH beta b
      (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfSection H hH u) y 1]
  simp only [
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfFourEdgeWord_fourCompanionSection]

/-- Exact section factorization of the **full** positive-boundary temporal
Wilson interaction.  Every residual plaquette is retained in the first finite
product, while all dependence on the four selected companion coordinates is
carried by the four explicit relative Wilson kernels in the second factor.

This is the finite-volume Fubini interface needed to isolate the protected
four-edge Fock sector without setting the residual interaction to the identity. -/
theorem
    periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoltzmannWeight_fourCompanionSection_eq_residualBoundaryProduct_mul_relativeKernelProduct
    (H : ℕ)
    (hH : 1 < H)
    (beta : ℝ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (u : Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoltzmannWeight H 2 beta
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
          b
          (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfSection
            H (Nat.zero_lt_of_lt hH) u)
          y) =
      (∏ p ∈ periodicHypercubicEvenPositiveBoundaryTemporalResidualPlaquettes H,
        specialUnitaryWilsonRelativeKernel 2 beta
          (periodicHypercubicEvenPositiveBoundaryTemporalFiberedBoundaryLeg b p)
          1) *
      ((specialUnitaryWilsonRelativeKernel 2 beta
          (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b 2) (u 2) *
        specialUnitaryWilsonRelativeKernel 2 beta
          (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b 3) (u 3)) *
       (specialUnitaryWilsonRelativeKernel 2 beta
          (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b 0) (u 0) *
        specialUnitaryWilsonRelativeKernel 2 beta
          (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b 1) (u 1))) := by
  rw [periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoltzmannWeight_eq_residual_mul_fourCompanion]
  rw [
    periodicHypercubicEvenPositiveBoundaryTemporalWilsonResidualWeight_fourCompanionSection_eq_boundaryProduct
      H hH beta b u y]
  rw [
    periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionWilsonWeight_fourCompanionSection_eq_relativeKernelProduct
      H (Nat.zero_lt_of_lt hH) beta b u y]

end

end MathlibAnalytic
end MGAP4D
