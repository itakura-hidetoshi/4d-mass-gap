import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonDobrushinRandomScanFiniteResolventTotal
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenDobrushinTransposeResolventGeometric
import Mathlib.Tactic

/-!
# Periodic geometric bound for the finite random-scan resolvent profile

This file combines the three finite ingredients already available for the
current periodic compact `SU(N)` Wilson system:

* the finite random-scan accumulated profile `w_M`;
* its transpose-Dobrushin subinvariance and uniform total-mass bound;
* geometric support of the recursive Dobrushin resolvent kernel.

For a nonnegative forcing profile `v` supported in `S`, and a link in a set `T`
plaquette-locally separated from `S` by at least `D`, the result is the finite,
uniform-in-`M` estimate

`w_M(e) ≤ rho^D / (1-rho) * ∑ i in S, v(i)`

with `rho = 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta`.

No infinite Poisson solution, covariance telescope, continuum limit, or
Hamiltonian mass-gap conclusion is used here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

private instance periodicHypercubicEvenSideLength_neZero_randomScanFiniteResolventGeometric
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) :=
  ⟨by simp [PeriodicHypercubicEvenSideLength]⟩

/-- A finite real profile supported in `S` has the same total sum as its sum
restricted to `S`. -/
theorem finite_sum_eq_sum_support_of_eq_zero_off
    {α : Type*}
    [Fintype α]
    [DecidableEq α]
    (S : Finset α)
    (v : α → ℝ)
    (hvSupport : ∀ i : α, i ∉ S → v i = 0) :
    (∑ i : α, v i) = ∑ i ∈ S, v i := by
  symm
  exact
    Finset.sum_subset (Finset.subset_univ S)
      (by
        intro i _ hi
        exact hvSupport i hi)

/-- The physical positive-link set of an even periodic four-dimensional box is
nonempty, hence its finite cardinality is positive. -/
theorem periodicHypercubicEvenEdge_card_pos (H : ℕ) :
    0 < Fintype.card (PeriodicHypercubicEvenEdge H) := by
  apply Fintype.card_pos_iff.mpr
  exact ⟨(0, 0)⟩

/-- The actual finite random-scan resolvent profile for the current periodic
compact `SU(N)` Dobrushin matrix already satisfies the sharp separated-support
geometric estimate, uniformly in the finite truncation length `M`. -/
theorem periodicHypercubicEvenSpecialUnitary_dobrushinRandomScanFiniteResolventProfile_le_geometric_of_supportsSeparatedBy
    (H N D : ℕ)
    (hH : 0 < H)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hBeta : 0 ≤ beta)
    (hThreshold :
      18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta < 1)
    (S T : Finset (PeriodicHypercubicEvenEdge H))
    (hsep : periodicHypercubicEvenSupportsPlaquetteLocalSeparatedBy H D S T)
    (v : PeriodicHypercubicEvenEdge H → ℝ)
    (hvNonneg : ∀ i : PeriodicHypercubicEvenEdge H, 0 ≤ v i)
    (hvSupport :
      ∀ i : PeriodicHypercubicEvenEdge H, i ∉ S → v i = 0)
    (M : ℕ)
    (source : PeriodicHypercubicEvenEdge H)
    (hsource : source ∈ T) :
    let Ddata :=
      periodicHypercubicSpecialUnitary_sparseDobrushinMatrixData_of_threshold
        (PeriodicHypercubicEvenSideLength H) N
        (by
          simp [PeriodicHypercubicEvenSideLength]
          omega)
        hN beta hBeta hThreshold
    let w :=
      continuousCompactOrientedGaugeWilsonDobrushinRandomScanFiniteResolventProfile
        Ddata v M
    w source ≤
      ((18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta) ^ D /
        (1 - 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta)) *
          ∑ i ∈ S, v i := by
  let Ddata :=
    periodicHypercubicSpecialUnitary_sparseDobrushinMatrixData_of_threshold
      (PeriodicHypercubicEvenSideLength H) N
      (by
        simp [PeriodicHypercubicEvenSideLength]
        omega)
      hN beta hBeta hThreshold
  let w :=
    continuousCompactOrientedGaugeWilsonDobrushinRandomScanFiniteResolventProfile
      Ddata v M
  have hEdge :
      0 < Fintype.card (PeriodicHypercubicEvenEdge H) :=
    periodicHypercubicEvenEdge_card_pos H
  have hw : ∀ i : PeriodicHypercubicEvenEdge H, 0 ≤ w i := by
    intro i
    exact
      continuous_compact_oriented_dobrushinRandomScanFiniteResolventProfile_nonneg
        Ddata v hvNonneg M i
  have hSub : ∀ s : PeriodicHypercubicEvenEdge H,
      w s ≤ v s +
        ∑ t : PeriodicHypercubicEvenEdge H,
          Ddata.influence t s * w t := by
    intro s
    exact
      continuous_compact_oriented_dobrushinRandomScanFiniteResolventProfile_subinvariant
        Ddata v hvNonneg hEdge M s
  have hCoeff : Ddata.coefficient < 1 := by
    simpa [Ddata,
      periodicHypercubicSpecialUnitary_sparseDobrushinMatrixData_of_threshold] using
      hThreshold
  have hTotalAll :=
    continuous_compact_oriented_dobrushinRandomScanFiniteResolventProfile_total_le_inv_gap_mul
      Ddata v hvNonneg hCoeff hEdge M
  have hvTotal :
      continuousCompactOrientedGaugeWilsonTotalVariation v =
        ∑ i ∈ S, v i := by
    unfold continuousCompactOrientedGaugeWilsonTotalVariation
    exact finite_sum_eq_sum_support_of_eq_zero_off S v hvSupport
  rw [hvTotal] at hTotalAll
  have hTotal :
      (∑ i : PeriodicHypercubicEvenEdge H, w i) ≤
        (1 - 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta)⁻¹ *
          ∑ i ∈ S, v i := by
    simpa [w, continuousCompactOrientedGaugeWilsonTotalVariation, Ddata,
      periodicHypercubicSpecialUnitary_sparseDobrushinMatrixData_of_threshold] using
      hTotalAll
  exact
    periodicHypercubicEvenSpecialUnitary_sparseDobrushinMatrixData_transposeSubinvariant_le_geometric_of_supportsSeparatedBy
      H N D hH hN beta hBeta hThreshold S T hsep v w hw hvSupport
      (by simpa [Ddata] using hSub) hTotal source hsource

end

end MathlibAnalytic
end MGAP4D
