import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonVacuumNormalizedH1D5TwoModeCrossingSelectedSectorPSD
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCyclicFourEdgeWilsonExactPSDStrictness
import Mathlib.Tactic

/-!
# H1-D5 crossing selected sector: residual scalar times four-edge Fock kernel

The preceding selected-sector layer protects one common positive Taylor/Fock
degree on the four links of the canonical primary spatial plaquette while
retaining degree zero on every other spatial link.

This file identifies that selected product exactly.  The residual links
contribute the genuine Wilson degree-zero scalar `exp (-beta)`; the four
primary links contribute the existing cyclic four-edge selected-degree kernel.
Thus the protected sector is

  exp (-beta) ^ residual.card * K_four-edge(selected).

No residual interaction is deleted and no remainder sign is assumed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- On every residual spatial link the selected term is exactly the genuine
degree-zero Wilson Taylor factor `exp (-beta)`. -/
theorem
    periodicHypercubicEvenPrimarySpatialSliceCrossingSelectedDegreeKernel_eq_exp_neg_of_mem_residual
    (H : ℕ)
    (beta : ℝ)
    (selected : ℕ)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (he :
      e ∈ periodicHypercubicEvenPrimarySpatialSlicePlaquetteResidualEdgeSet H)
    (g h : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    specialUnitaryWilsonRelativeSelectedDegreeKernel 2 beta
        (periodicHypercubicEvenPrimarySpatialSliceCrossingSelectedDegreeAssignment
          H selected e) g h =
      Real.exp (-beta) := by
  rw [
    periodicHypercubicEvenPrimarySpatialSliceCrossingSelectedDegreeAssignment_eq_zero_of_mem_residual
      H selected e he]
  simp [specialUnitaryWilsonRelativeSelectedDegreeKernel,
    specialUnitaryWilsonSelectedTaylorCoefficient]

/-- The selected product on the four actual primary-spatial links is exactly
the existing genuine cyclic four-edge selected Fock kernel. -/
theorem
    periodicHypercubicEvenPrimarySpatialSlicePlaquetteSelectedDegreeProduct_eq_cyclicFourEdge
    (H : ℕ)
    (beta : ℝ)
    (selected : ℕ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    (∏ e ∈ periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdgeSet H,
      specialUnitaryWilsonRelativeSelectedDegreeKernel
        2 beta selected (A e) (B e)) =
      specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeKernel beta selected
        (fun k => A (periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdge H k))
        (fun k => B (periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdge H k)) := by
  classical
  rw [
    ← specialUnitaryTwoCyclicFourEdgeWilsonSelectedCoordinateProductKernel_eq_selectedDegree]
  simp +decide [
    periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdgeSet,
    periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdgeEmbedding,
    specialUnitaryTwoCyclicFourEdgeWilsonSelectedCoordinateProductKernel,
    Fin.prod_univ_succ] <;> ring

/-- Exact selected-product factorization on the complete literal crossing-link
carrier. -/
theorem
    periodicHypercubicEvenPrimarySpatialSliceCrossingSelectedDegreeProduct_eq_residualScalar_mul_fourEdgeSelectedDegreeKernel
    (H : ℕ)
    (beta : ℝ)
    (selected : ℕ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    (∏ e ∈ periodicHypercubicEvenSpatialSliceLinkSet H,
      specialUnitaryWilsonRelativeSelectedDegreeKernel 2 beta
        (periodicHypercubicEvenPrimarySpatialSliceCrossingSelectedDegreeAssignment
          H selected e) (A e) (B e)) =
      (Real.exp (-beta)) ^
          (periodicHypercubicEvenPrimarySpatialSlicePlaquetteResidualEdgeSet H).card *
        specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeKernel beta selected
          (fun k => A
            (periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdge H k))
          (fun k => B
            (periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdge H k)) := by
  classical
  let full := periodicHypercubicEvenSpatialSliceLinkSet H
  let primary := periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdgeSet H
  let residual :=
    periodicHypercubicEvenPrimarySpatialSlicePlaquetteResidualEdgeSet H
  let f : PeriodicHypercubicEvenSpatialSliceLink H → ℝ := fun e =>
    specialUnitaryWilsonRelativeSelectedDegreeKernel 2 beta
      (periodicHypercubicEvenPrimarySpatialSliceCrossingSelectedDegreeAssignment
        H selected e) (A e) (B e)
  have hsubset : primary ⊆ full := by
    intro e he
    dsimp [full, periodicHypercubicEvenSpatialSliceLinkSet]
    exact List.mem_toFinset.mpr
      (periodicHypercubicEvenSpatialSliceLink_mem_list H e)
  have hunion : residual ∪ primary = full := by
    simpa [residual, primary, full,
      periodicHypercubicEvenPrimarySpatialSlicePlaquetteResidualEdgeSet] using
      (Finset.sdiff_union_of_subset hsubset)
  have hdisjoint : Disjoint residual primary := by
    refine Finset.disjoint_left.mpr ?_
    intro e heResidual hePrimary
    have heDiff : e ∈ full \ primary := by
      simpa [residual, full, primary,
        periodicHypercubicEvenPrimarySpatialSlicePlaquetteResidualEdgeSet] using
        heResidual
    exact (Finset.mem_sdiff.mp heDiff).2 hePrimary
  have hproduct :
      (∏ e ∈ full, f e) =
        (∏ e ∈ residual, f e) * (∏ e ∈ primary, f e) := by
    rw [← hunion]
    exact Finset.prod_union hdisjoint
  have hresidual :
      (∏ e ∈ residual, f e) =
        (Real.exp (-beta)) ^ residual.card := by
    calc
      (∏ e ∈ residual, f e) =
          ∏ _e ∈ residual, Real.exp (-beta) := by
            apply Finset.prod_congr rfl
            intro e he
            dsimp [f]
            exact
              periodicHypercubicEvenPrimarySpatialSliceCrossingSelectedDegreeKernel_eq_exp_neg_of_mem_residual
                H beta selected e
                (by simpa [residual] using he)
                (A e) (B e)
      _ = (Real.exp (-beta)) ^ residual.card := by simp
  have hprimaryAssignment :
      (∏ e ∈ primary, f e) =
        ∏ e ∈ primary,
          specialUnitaryWilsonRelativeSelectedDegreeKernel
            2 beta selected (A e) (B e) := by
    apply Finset.prod_congr rfl
    intro e he
    have hePrimary :
        e ∈ periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdgeSet H := by
      simpa [primary] using he
    simp [f,
      periodicHypercubicEvenPrimarySpatialSliceCrossingSelectedDegreeAssignment,
      hePrimary]
  have hprimary :
      (∏ e ∈ primary, f e) =
        specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeKernel beta selected
          (fun k => A
            (periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdge H k))
          (fun k => B
            (periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdge H k)) := by
    rw [hprimaryAssignment]
    simpa [primary] using
      periodicHypercubicEvenPrimarySpatialSlicePlaquetteSelectedDegreeProduct_eq_cyclicFourEdge
        H beta selected A B
  change
    (∏ e ∈ full, f e) =
      (Real.exp (-beta)) ^ residual.card *
        specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeKernel beta selected
          (fun k => A
            (periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdge H k))
          (fun k => B
            (periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdge H k))
  rw [hproduct, hresidual, hprimary]

/-- The retained residual degree-zero coefficient is strictly positive. -/
theorem
    periodicHypercubicEvenPrimarySpatialSliceCrossingResidualDegreeZeroScalar_pos
    (H : ℕ)
    (beta : ℝ) :
    0 < (Real.exp (-beta)) ^
      (periodicHypercubicEvenPrimarySpatialSlicePlaquetteResidualEdgeSet H).card := by
  positivity

/-- The exact temporal crossing kernel dominates the explicit residual-scalar
multiple of the genuine primary four-edge selected Fock kernel in the Schur
PSD cone. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTwoTemporalGaugeCrossingKernel_sub_residualScalar_mul_primaryFourEdgeSelectedDegreeKernel_positiveSemidefiniteCertificate
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (selected : ℕ) :
    RealKernelPositiveSemidefiniteCertificate
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
      (fun A B =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
            H 2 beta A B -
          (Real.exp (-beta)) ^
              (periodicHypercubicEvenPrimarySpatialSlicePlaquetteResidualEdgeSet H).card *
            specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeKernel beta selected
              (fun k => A
                (periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdge H k))
              (fun k => B
                (periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdge H k))) := by
  have C :=
    periodicHypercubicEvenSpecialUnitaryTwoTemporalGaugeCrossingKernel_sub_primarySelectedDegreeProduct_positiveSemidefiniteCertificate
      H beta hbeta selected
  have hkernel :
      (fun A B :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
            H 2 beta A B -
          ∏ e ∈ periodicHypercubicEvenSpatialSliceLinkSet H,
            specialUnitaryWilsonRelativeSelectedDegreeKernel 2 beta
              (periodicHypercubicEvenPrimarySpatialSliceCrossingSelectedDegreeAssignment
                H selected e) (A e) (B e)) =
      (fun A B =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
            H 2 beta A B -
          (Real.exp (-beta)) ^
              (periodicHypercubicEvenPrimarySpatialSlicePlaquetteResidualEdgeSet H).card *
            specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeKernel beta selected
              (fun k => A
                (periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdge H k))
              (fun k => B
                (periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdge H k))) := by
    funext A B
    rw [
      periodicHypercubicEvenPrimarySpatialSliceCrossingSelectedDegreeProduct_eq_residualScalar_mul_fourEdgeSelectedDegreeKernel
        H beta selected A B]
  rw [← hkernel]
  exact C

end

end MathlibAnalytic
end MGAP4D
