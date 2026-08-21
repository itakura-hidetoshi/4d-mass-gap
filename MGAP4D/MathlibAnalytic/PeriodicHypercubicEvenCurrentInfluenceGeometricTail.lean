import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCurrentInfluenceWalkIterateIdentification
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Finite geometric tails of the current influence kernel

The preceding same-root layer identifies the explicit endpoint-constrained
influence-walk kernel with the recursive finite Dobrushin iterate.  It also
places two complementary facts on that same finite kernel:

* actual plaquette-local support separation kills every degree below the
  separation distance exactly;
* a strict current Dobrushin coefficient bounds every degree by a geometric
  power.

This file packages those facts into a finite Neumann-tail carrier.  For
`0 <= c < 1`, every finite geometric tail beginning at degree `D` is bounded by
`c^D / (1 - c)`.  Hence a current compact Dobrushin iterate has the same bound,
while actual support separation gives an exact zero prefix below `D`.

The periodic compact `SU(N)` specialization combines both statements under the
existing explicit finite-volume threshold.  The physical midpoint-support
scaling specialization only records the exact-zero prefix and leaves the
coupling sequence arbitrary.

This is still finite influence-kernel algebra.  No covariance representation,
continuum clustering, positive physical mass, OS Hamiltonian gap, or
factorial-continuum Dobrushin condition is asserted here.  Markov update time is
not identified with Euclidean time.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter
open scoped BigOperators

noncomputable section

/-- A finite geometric tail beginning at degree `D` is bounded uniformly in its
truncation length by the full geometric tail. -/
theorem finite_geometric_tail_sum_le
    (c : ℝ)
    (hc0 : 0 ≤ c)
    (hc1 : c < 1)
    (D M : ℕ) :
    (∑ k in Finset.range M, c ^ (D + k)) ≤ c ^ D / (1 - c) := by
  have hsum :
      HasSum (fun k : ℕ => c ^ (D + k)) (c ^ D / (1 - c)) := by
    simpa [pow_add, div_eq_mul_inv] using
      (HasSum.mul_left (c ^ D) (hasSum_geometric_of_lt_one hc0 hc1))
  exact
    sum_le_hasSum
      (Finset.range M)
      (fun k _ => pow_nonneg hc0 (D + k))
      hsum

/-- A strict current compact Dobrushin coefficient gives a uniform finite
Neumann-tail bound for every matrix entry. -/
theorem continuous_compact_oriented_dobrushin_influenceIterateKernel_tail_le_geometric
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (data : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (hStrict : data.coefficient < 1)
    (D M : ℕ)
    (target source : C.base.geometry.Edge) :
    (∑ k in Finset.range M,
      finiteInfluenceIterateKernel data.influence (D + k) target source) ≤
        data.coefficient ^ D / (1 - data.coefficient) := by
  calc
    (∑ k in Finset.range M,
        finiteInfluenceIterateKernel data.influence (D + k) target source) ≤
      ∑ k in Finset.range M, data.coefficient ^ (D + k) := by
        apply Finset.sum_le_sum
        intro k _
        exact
          continuous_compact_oriented_dobrushin_influenceIterateKernel_le_pow
            C data (D + k) target source
    _ ≤ data.coefficient ^ D / (1 - data.coefficient) :=
      finite_geometric_tail_sum_le
        data.coefficient data.coefficient_nonneg hStrict D M

/-- Actual support separation makes the complete finite iterate prefix below
`D` vanish exactly. -/
theorem finiteInfluenceIterateKernel_prefix_sum_eq_zero_of_supportsSeparatedBy
    (H D : ℕ)
    (S T : Finset (PeriodicHypercubicEvenEdge H))
    (influence :
      PeriodicHypercubicEvenEdge H → PeriodicHypercubicEvenEdge H → ℝ)
    (hLocal :
      ∀ target source : PeriodicHypercubicEvenEdge H,
        influence target source ≠ 0 →
          periodicHypercubicEvenPlaquetteLocal H target source)
    (hsep : periodicHypercubicEvenSupportsPlaquetteLocalSeparatedBy H D S T)
    (target : PeriodicHypercubicEvenEdge H)
    (htarget : target ∈ S)
    (source : PeriodicHypercubicEvenEdge H)
    (hsource : source ∈ T) :
    (∑ d in Finset.range D,
      finiteInfluenceIterateKernel influence d target source) = 0 := by
  apply Finset.sum_eq_zero
  intro d hd
  exact
    finiteInfluenceIterateKernel_eq_zero_of_supportsSeparatedBy
      H D d S T influence hLocal hsep (Finset.mem_range.mp hd)
      target htarget source hsource

/-- Same-root scaling makes the entire fixed sub-distance iterate prefix
vanish eventually between the literal physical midpoint supports.  The coupling
sequence remains arbitrary. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointSupports_eventually_sparseActiveTVInfluenceIterateKernel_prefix_sum_eq_zero_of_scaling
    (H : ℕ → ℕ)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero : Tendsto latticeSpacing atTop (nhds 0))
    (hreach :
      Tendsto
        (periodicHypercubicEvenPrimarySpatialPhysicalTemporalReach H latticeSpacing)
        atTop atTop)
    (J : Finset ℚ)
    (hJ : ∀ q : ℚ, q ∈ J → 0 ≤ q)
    (r : ℚ)
    (hr : 0 < r)
    (beta : ℕ → ℝ)
    (D : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ∀ target : PeriodicHypercubicEvenEdge (H n),
        target ∈
          periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftReflectedSupport
            (H n) latticeSpacing n J →
        ∀ source : PeriodicHypercubicEvenEdge (H n),
          source ∈
            periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightSupport
              (H n) latticeSpacing n J r →
          (∑ d in Finset.range D,
            finiteInfluenceIterateKernel
              (fun target source =>
                periodicHypercubicSpecialUnitarySparseActiveTVInfluence
                  (PeriodicHypercubicEvenSideLength (H n)) (beta n) target source)
              d target source) = 0 := by
  have hZero :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointSupports_eventually_sparseActiveTVInfluenceIterateKernel_eq_zero_of_scaling
      H latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero hreach
      J hJ r hr beta D
  filter_upwards [hZero] with n hn
  intro target htarget source hsource
  apply Finset.sum_eq_zero
  intro d hd
  exact hn d (Finset.mem_range.mp hd) target htarget source hsource

private instance periodicHypercubicEvenSideLength_neZero_geometricTail
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) :=
  ⟨by simp [PeriodicHypercubicEvenSideLength]⟩

/-- Under the explicit finite-volume current compact `SU(N)` threshold, actual
support separation and coefficient decay combine on one recursive finite
kernel: the prefix below `D` is exactly zero and every finite tail beginning at
`D` is bounded by the full geometric tail. -/
theorem periodicHypercubicEvenSpecialUnitary_sparseDobrushinMatrixData_prefix_zero_and_tail_le_geometric_of_supportsSeparatedBy
    (H N D M : ℕ)
    (hH : 0 < H)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hBeta : 0 ≤ beta)
    (hThreshold :
      18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta < 1)
    (S T : Finset (PeriodicHypercubicEvenEdge H))
    (hsep : periodicHypercubicEvenSupportsPlaquetteLocalSeparatedBy H D S T)
    (target : PeriodicHypercubicEvenEdge H)
    (htarget : target ∈ S)
    (source : PeriodicHypercubicEvenEdge H)
    (hsource : source ∈ T) :
    let data :=
      periodicHypercubicSpecialUnitary_sparseDobrushinMatrixData_of_threshold
        (PeriodicHypercubicEvenSideLength H) N
        (by
          simp [PeriodicHypercubicEvenSideLength]
          omega)
        hN beta hBeta hThreshold
    ((∑ d in Finset.range D,
        finiteInfluenceIterateKernel data.influence d target source) = 0) ∧
      ((∑ k in Finset.range M,
          finiteInfluenceIterateKernel data.influence (D + k) target source) ≤
        (18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta) ^ D /
          (1 - 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta)) := by
  dsimp only
  constructor
  · apply Finset.sum_eq_zero
    intro d hd
    exact
      periodicHypercubicEvenSpecialUnitary_sparseDobrushinMatrixData_influenceIterateKernel_eq_zero_of_supportsSeparatedBy
        H N D d hH hN beta hBeta hThreshold S T hsep
        (Finset.mem_range.mp hd) target htarget source hsource
  · let C :=
      periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hBeta
    let data :=
      periodicHypercubicSpecialUnitary_sparseDobrushinMatrixData_of_threshold
        (PeriodicHypercubicEvenSideLength H) N
        (by
          simp [PeriodicHypercubicEvenSideLength]
          omega)
        hN beta hBeta hThreshold
    have hStrict : data.coefficient < 1 := by
      simpa [data,
        periodicHypercubicSpecialUnitary_sparseDobrushinMatrixData_of_threshold] using
        hThreshold
    have hTail :=
      continuous_compact_oriented_dobrushin_influenceIterateKernel_tail_le_geometric
        C data hStrict D M target source
    simpa [C, data,
      periodicHypercubicSpecialUnitary_sparseDobrushinMatrixData_of_threshold] using
      hTail

end

end MathlibAnalytic
end MGAP4D
