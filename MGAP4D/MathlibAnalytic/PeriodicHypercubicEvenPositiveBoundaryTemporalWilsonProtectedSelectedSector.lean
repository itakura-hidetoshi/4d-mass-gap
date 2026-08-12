import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPositiveBoundaryTemporalWilsonSelectedSectorPSD

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

private theorem positiveBoundaryTemporalWilsonProtectedSelectedSectorTwoRankPositive :
    0 < (2 : ℕ) := by
  norm_num

local instance positiveBoundaryTemporalWilsonProtectedSelectedSectorSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

/-- The exact full positive-boundary temporal Wilson product dominates the
strictly positive residual degree-zero scalar times the genuine four-edge
selected-degree Fock kernel in the Schur PSD cone.

This is the cancellation-free protection statement for the selected strict
component: all non-selected plaquettes remain present through their literal
degree-zero Fock factors, while every omitted higher-degree contribution is
absorbed into a PSD remainder. -/
theorem periodicHypercubicEvenPositiveBoundaryTemporalWilsonFullProduct_sub_residualScalar_mul_fourEdgeSelectedDegreeKernel_positiveSemidefiniteCertificate
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (selected : ℕ) :
    RealKernelPositiveSemidefiniteCertificate
      (PeriodicHypercubicEvenPlaquette H →
        Matrix.specialUnitaryGroup (Fin 2) ℂ)
      (fun u v =>
        (∏ p ∈ periodicHypercubicEvenPositiveBoundaryTemporalPlaquettes H,
          specialUnitaryWilsonRelativeKernel 2 beta (u p) (v p)) -
        (Real.exp (-beta)) ^
            (periodicHypercubicEvenPositiveBoundaryTemporalResidualPlaquettes H).card *
          specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeKernel beta selected
            (fun k => u
              (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k))
            (fun k => v
              (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k))) := by
  have C :=
    periodicHypercubicEvenPositiveBoundaryTemporalWilsonFullProduct_sub_selectedDegreeProduct_positiveSemidefiniteCertificate
      H beta hbeta selected
  have hkernel :
      (fun u v : PeriodicHypercubicEvenPlaquette H →
          Matrix.specialUnitaryGroup (Fin 2) ℂ =>
        (∏ p ∈ periodicHypercubicEvenPositiveBoundaryTemporalPlaquettes H,
          specialUnitaryWilsonRelativeKernel 2 beta (u p) (v p)) -
        ∏ p ∈ periodicHypercubicEvenPositiveBoundaryTemporalPlaquettes H,
          specialUnitaryWilsonRelativeSelectedDegreeKernel 2 beta
            (periodicHypercubicEvenPositiveBoundaryTemporalWilsonSelectedDegreeAssignment
              H selected p) (u p) (v p)) =
      (fun u v =>
        (∏ p ∈ periodicHypercubicEvenPositiveBoundaryTemporalPlaquettes H,
          specialUnitaryWilsonRelativeKernel 2 beta (u p) (v p)) -
        (Real.exp (-beta)) ^
            (periodicHypercubicEvenPositiveBoundaryTemporalResidualPlaquettes H).card *
          specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeKernel beta selected
            (fun k => u
              (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k))
            (fun k => v
              (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k))) := by
    funext u v
    rw [periodicHypercubicEvenPositiveBoundaryTemporalWilsonSelectedDegreeProduct_eq_residualScalar_mul_fourEdgeSelectedDegreeKernel]
  rw [← hkernel]
  exact C

/-- Pointwise exact protected-component decomposition of the full literal
positive-boundary temporal Wilson product. -/
theorem periodicHypercubicEvenPositiveBoundaryTemporalWilsonFullProduct_eq_protectedRemainder_add_residualScalar_mul_fourEdgeSelectedDegreeKernel
    (H : ℕ)
    (beta : ℝ)
    (selected : ℕ)
    (u v : PeriodicHypercubicEvenPlaquette H →
      Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    (∏ p ∈ periodicHypercubicEvenPositiveBoundaryTemporalPlaquettes H,
      specialUnitaryWilsonRelativeKernel 2 beta (u p) (v p)) =
      ((∏ p ∈ periodicHypercubicEvenPositiveBoundaryTemporalPlaquettes H,
          specialUnitaryWilsonRelativeKernel 2 beta (u p) (v p)) -
        (Real.exp (-beta)) ^
            (periodicHypercubicEvenPositiveBoundaryTemporalResidualPlaquettes H).card *
          specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeKernel beta selected
            (fun k => u
              (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k))
            (fun k => v
              (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k))) +
      (Real.exp (-beta)) ^
          (periodicHypercubicEvenPositiveBoundaryTemporalResidualPlaquettes H).card *
        specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeKernel beta selected
          (fun k => u
            (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k))
          (fun k => v
            (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k)) := by
  ring

/-- The protected four-edge selected component carries a strictly positive
scalar coefficient for every coupling. -/
theorem periodicHypercubicEvenPositiveBoundaryTemporalWilsonProtectedSelectedCoefficient_pos
    (H : ℕ)
    (beta : ℝ) :
    0 < (Real.exp (-beta)) ^
      (periodicHypercubicEvenPositiveBoundaryTemporalResidualPlaquettes H).card :=
  periodicHypercubicEvenPositiveBoundaryTemporalWilsonResidualDegreeZeroScalar_pos H beta

end

end MathlibAnalytic
end MGAP4D
