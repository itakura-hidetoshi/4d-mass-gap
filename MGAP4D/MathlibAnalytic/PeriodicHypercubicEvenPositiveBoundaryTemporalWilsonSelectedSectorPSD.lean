import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPositiveBoundaryTemporalWilsonResidualProduct
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCyclicFourEdgeWilsonExactPSDStrictness
import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonFiniteSelectedSectorPSD
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

private theorem positiveBoundaryTemporalWilsonSelectedSectorTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance positiveBoundaryTemporalWilsonSelectedSectorSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

/-- Degree assignment on the literal positive-boundary temporal plaquette
sector.  The four canonical companions carry the selected positive degree;
every other actual positive-boundary plaquette carries the genuine Fock
degree-zero component. -/
noncomputable def periodicHypercubicEvenPositiveBoundaryTemporalWilsonSelectedDegreeAssignment
    (H : ℕ)
    (selected : ℕ)
    (p : PeriodicHypercubicEvenPlaquette H) : ℕ := by
  classical
  exact if p ∈ periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionSet H then
    selected else 0

@[simp]
theorem periodicHypercubicEvenPositiveBoundaryTemporalWilsonSelectedDegreeAssignment_companion
    (H : ℕ)
    (selected : ℕ)
    (k : Fin 4) :
    periodicHypercubicEvenPositiveBoundaryTemporalWilsonSelectedDegreeAssignment
        H selected
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k) =
      selected := by
  classical
  simp [periodicHypercubicEvenPositiveBoundaryTemporalWilsonSelectedDegreeAssignment]

/-- Every literal residual plaquette is assigned degree zero.  This is a
retained Fock sector, not deletion of the residual interaction. -/
theorem periodicHypercubicEvenPositiveBoundaryTemporalWilsonSelectedDegreeAssignment_eq_zero_of_mem_residual
    (H : ℕ)
    (selected : ℕ)
    (p : PeriodicHypercubicEvenPlaquette H)
    (hp : p ∈ periodicHypercubicEvenPositiveBoundaryTemporalResidualPlaquettes H) :
    periodicHypercubicEvenPositiveBoundaryTemporalWilsonSelectedDegreeAssignment
        H selected p = 0 := by
  classical
  have hnot :
      p ∉ periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionSet H :=
    (Finset.mem_sdiff.mp hp).2
  simp [periodicHypercubicEvenPositiveBoundaryTemporalWilsonSelectedDegreeAssignment, hnot]

/-- On a residual plaquette, the selected factor is exactly the actual
one-plaquette degree-zero Wilson Taylor sector `exp (-beta)`. -/
theorem periodicHypercubicEvenPositiveBoundaryTemporalWilsonSelectedDegreeKernel_eq_exp_neg_of_mem_residual
    (H : ℕ)
    (beta : ℝ)
    (selected : ℕ)
    (p : PeriodicHypercubicEvenPlaquette H)
    (hp : p ∈ periodicHypercubicEvenPositiveBoundaryTemporalResidualPlaquettes H)
    (g h : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    specialUnitaryWilsonRelativeSelectedDegreeKernel 2 beta
        (periodicHypercubicEvenPositiveBoundaryTemporalWilsonSelectedDegreeAssignment
          H selected p) g h =
      Real.exp (-beta) := by
  rw [periodicHypercubicEvenPositiveBoundaryTemporalWilsonSelectedDegreeAssignment_eq_zero_of_mem_residual
    H selected p hp]
  simp [specialUnitaryWilsonRelativeSelectedDegreeKernel,
    specialUnitaryWilsonSelectedTaylorCoefficient]

/-- The full literal positive-boundary Wilson relative-kernel product dominates
the degree-assigned selected product in the Schur PSD cone.  The selected
product keeps the four companion degree-`selected` factors and the actual
degree-zero factors on the literal residual complement. -/
theorem periodicHypercubicEvenPositiveBoundaryTemporalWilsonFullProduct_sub_selectedDegreeProduct_positiveSemidefiniteCertificate
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
        ∏ p ∈ periodicHypercubicEvenPositiveBoundaryTemporalPlaquettes H,
          specialUnitaryWilsonRelativeSelectedDegreeKernel 2 beta
            (periodicHypercubicEvenPositiveBoundaryTemporalWilsonSelectedDegreeAssignment
              H selected p) (u p) (v p)) := by
  exact
    specialUnitaryWilsonRelativeKernel_finsetProd_sub_selectedDegreeProd_positiveSemidefiniteCertificate
      2 positiveBoundaryTemporalWilsonSelectedSectorTwoRankPositive beta hbeta
      (periodicHypercubicEvenPositiveBoundaryTemporalPlaquettes H)
      (periodicHypercubicEvenPositiveBoundaryTemporalWilsonSelectedDegreeAssignment
        H selected)

/-- The selected product on the actual four-companion block is exactly the
four independent selected-coordinate product already used by the strict
four-edge Wilson/Fock sector.  No cyclic-composite kernel is introduced. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionSelectedDegreeProduct_eq_cyclicFourEdge
    (H : ℕ)
    (beta : ℝ)
    (selected : ℕ)
    (u v : PeriodicHypercubicEvenPlaquette H →
      Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    (∏ p ∈ periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionSet H,
      specialUnitaryWilsonRelativeSelectedDegreeKernel 2 beta selected
        (u p) (v p)) =
      specialUnitaryTwoCyclicFourEdgeWilsonSelectedCoordinateProductKernel beta selected
        (fun k => u
          (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k))
        (fun k => v
          (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k)) := by
  classical
  simp +decide [periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionSet,
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionEmbedding,
    specialUnitaryTwoCyclicFourEdgeWilsonSelectedCoordinateProductKernel,
    Fin.prod_univ_succ] <;> ring

/-- Hence the literal selected companion product is exactly the genuine
four-edge diagonal Fock kernel from the strictness package. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionSelectedDegreeProduct_eq_selectedDegreeKernel
    (H : ℕ)
    (beta : ℝ)
    (selected : ℕ)
    (u v : PeriodicHypercubicEvenPlaquette H →
      Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    (∏ p ∈ periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionSet H,
      specialUnitaryWilsonRelativeSelectedDegreeKernel 2 beta selected
        (u p) (v p)) =
      specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeKernel beta selected
        (fun k => u
          (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k))
        (fun k => v
          (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k)) := by
  rw [periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionSelectedDegreeProduct_eq_cyclicFourEdge]
  exact
    specialUnitaryTwoCyclicFourEdgeWilsonSelectedCoordinateProductKernel_eq_selectedDegree
      beta selected _ _

end

end MathlibAnalytic
end MGAP4D
