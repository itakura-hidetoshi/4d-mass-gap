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

/-- The selected product on the entire literal positive-boundary temporal
sector factors exactly into the retained residual degree-zero scalar and the
genuine four-edge selected Fock kernel.  Thus the unselected interaction is
kept as an actual degree-zero Fock component rather than replaced by `1`. -/
theorem periodicHypercubicEvenPositiveBoundaryTemporalWilsonSelectedDegreeProduct_eq_residualScalar_mul_fourEdgeSelectedDegreeKernel
    (H : ℕ)
    (beta : ℝ)
    (selected : ℕ)
    (u v : PeriodicHypercubicEvenPlaquette H →
      Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    (∏ p ∈ periodicHypercubicEvenPositiveBoundaryTemporalPlaquettes H,
      specialUnitaryWilsonRelativeSelectedDegreeKernel 2 beta
        (periodicHypercubicEvenPositiveBoundaryTemporalWilsonSelectedDegreeAssignment
          H selected p) (u p) (v p)) =
      (Real.exp (-beta)) ^
          (periodicHypercubicEvenPositiveBoundaryTemporalResidualPlaquettes H).card *
        specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeKernel beta selected
          (fun k => u
            (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k))
          (fun k => v
            (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k)) := by
  classical
  let full := periodicHypercubicEvenPositiveBoundaryTemporalPlaquettes H
  let companions := periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionSet H
  let residual := periodicHypercubicEvenPositiveBoundaryTemporalResidualPlaquettes H
  let f : PeriodicHypercubicEvenPlaquette H → ℝ := fun p =>
    specialUnitaryWilsonRelativeSelectedDegreeKernel 2 beta
      (periodicHypercubicEvenPositiveBoundaryTemporalWilsonSelectedDegreeAssignment
        H selected p) (u p) (v p)
  have hsubset : companions ⊆ full := by
    simpa [companions, full] using
      periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionSet_subset_positiveBoundary H
  have hunion : residual ∪ companions = full := by
    simpa [residual, companions, full,
      periodicHypercubicEvenPositiveBoundaryTemporalResidualPlaquettes] using
      (Finset.sdiff_union_of_subset hsubset)
  have hdisjoint : Disjoint residual companions := by
    refine Finset.disjoint_left.mpr ?_
    intro p hpResidual hpCompanion
    have hpDiff : p ∈ full \ companions := by
      simpa [residual, full, companions,
        periodicHypercubicEvenPositiveBoundaryTemporalResidualPlaquettes] using hpResidual
    exact (Finset.mem_sdiff.mp hpDiff).2 hpCompanion
  have hproduct :
      (∏ p ∈ full, f p) =
        (∏ p ∈ residual, f p) * (∏ p ∈ companions, f p) := by
    rw [← hunion]
    exact Finset.prod_union hdisjoint
  have hresidual :
      (∏ p ∈ residual, f p) =
        (Real.exp (-beta)) ^ residual.card := by
    calc
      (∏ p ∈ residual, f p) =
          ∏ _p ∈ residual, Real.exp (-beta) := by
            apply Finset.prod_congr rfl
            intro p hp
            dsimp [f]
            exact
              periodicHypercubicEvenPositiveBoundaryTemporalWilsonSelectedDegreeKernel_eq_exp_neg_of_mem_residual
                H beta selected p
                  (by simpa [residual] using hp) (u p) (v p)
      _ = (Real.exp (-beta)) ^ residual.card := by simp
  have hcompanionsAssignment :
      (∏ p ∈ companions, f p) =
        ∏ p ∈ companions,
          specialUnitaryWilsonRelativeSelectedDegreeKernel 2 beta selected
            (u p) (v p) := by
    apply Finset.prod_congr rfl
    intro p hp
    have hpCompanion :
        p ∈ periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionSet H := by
      simpa [companions] using hp
    simp [f,
      periodicHypercubicEvenPositiveBoundaryTemporalWilsonSelectedDegreeAssignment,
      hpCompanion]
  have hcompanions :
      (∏ p ∈ companions, f p) =
        specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeKernel beta selected
          (fun k => u
            (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k))
          (fun k => v
            (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k)) := by
    rw [hcompanionsAssignment]
    simpa [companions] using
      periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionSelectedDegreeProduct_eq_selectedDegreeKernel
        H beta selected u v
  change
    (∏ p ∈ full, f p) =
      (Real.exp (-beta)) ^ residual.card *
        specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeKernel beta selected
          (fun k => u
            (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k))
          (fun k => v
            (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k))
  rw [hproduct, hresidual, hcompanions]

/-- The literal residual degree-zero scalar multiplying the four-edge selected
sector is strictly positive. -/
theorem periodicHypercubicEvenPositiveBoundaryTemporalWilsonResidualDegreeZeroScalar_pos
    (H : ℕ)
    (beta : ℝ) :
    0 < (Real.exp (-beta)) ^
      (periodicHypercubicEvenPositiveBoundaryTemporalResidualPlaquettes H).card := by
  positivity

end

end MathlibAnalytic
end MGAP4D
