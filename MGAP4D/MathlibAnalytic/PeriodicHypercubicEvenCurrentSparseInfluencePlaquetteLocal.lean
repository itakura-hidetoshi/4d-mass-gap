import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenMidpointWilsonSourceScalingSeparation
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonCenteredVariationPropagation
import Mathlib.Tactic

/-!
# Current sparse SU(N) influence is actual plaquette-local

The same-root midpoint route now has an actual Wilson-plaquette-local path
geometry and, under scaling, arbitrarily large fixed support separation.  The
current compact `SU(N)` Dobrushin route separately has a sparse one-link
conditional-TV influence supported on `periodicHypercubicActiveNeighbors`.

This file identifies those two finite geometries without reviving the
historical finite-gauge Dobrushin stack.

* every active-neighbor pair is local in one actual Wilson plaquette;
* therefore the current sparse active-TV influence vanishes on every non-local
  physical-link pair;
* support separation by two steps kills every direct sparse influence between
  the two supports;
* the scaling theorem from the preceding layer therefore eventually kills all
  direct sparse influences between the literal midpoint supports;
* under the explicit finite-volume high-temperature threshold, the same
  locality statement holds for the current compact `DobrushinMatrixData`
  influence itself.

This is an influence-graph locality statement, not a covariance decay theorem.
The threshold is not asserted along the factorial continuum coupling sequence,
and no heat-bath/update time is identified with physical OS Euclidean time.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

private instance periodicHypercubicEvenSideLength_neZero_current
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) :=
  ⟨by simp [PeriodicHypercubicEvenSideLength]⟩

/-- Every current periodic active-neighbor pair occurs in one actual Wilson
plaquette, hence is local in the #1934 physical-link relation. -/
theorem periodicHypercubicEvenPlaquetteLocal_of_mem_activeNeighbors_current
    (H : ℕ)
    (target source : PeriodicHypercubicEvenEdge H)
    (hActive :
      source ∈
        periodicHypercubicActiveNeighbors
          (PeriodicHypercubicEvenSideLength H) target) :
    periodicHypercubicEvenPlaquetteLocal H target source := by
  classical
  have hWitness :=
    (periodicHypercubic_mem_activeNeighbors_iff_for_compactSU
      (PeriodicHypercubicEvenSideLength H) target source).mp hActive
  rcases hWitness.1 with ⟨p, hpTarget, hpSource⟩
  refine ⟨p, ?_, ?_⟩
  · have hmem :=
      periodicHypercubic_mem_plaquetteEdges_of_touches
        (PeriodicHypercubicEvenSideLength H) p target hpTarget
    simpa [periodicHypercubicEvenPlaquetteEdgeSupport,
      periodicHypercubicPlaquetteEdges,
      periodicHypercubicPhysicalBoundaryEdge] using hmem
  · have hmem :=
      periodicHypercubic_mem_plaquetteEdges_of_touches
        (PeriodicHypercubicEvenSideLength H) p source hpSource
    simpa [periodicHypercubicEvenPlaquetteEdgeSupport,
      periodicHypercubicPlaquetteEdges,
      periodicHypercubicPhysicalBoundaryEdge] using hmem

/-- The current sparse active-TV influence is exactly zero on every pair that
is not local in one actual Wilson plaquette. -/
theorem periodicHypercubicEvenSpecialUnitarySparseActiveTVInfluence_eq_zero_of_not_plaquetteLocal
    (H : ℕ)
    (beta : ℝ)
    (target source : PeriodicHypercubicEvenEdge H)
    (hNotLocal : ¬ periodicHypercubicEvenPlaquetteLocal H target source) :
    periodicHypercubicSpecialUnitarySparseActiveTVInfluence
      (PeriodicHypercubicEvenSideLength H) beta target source = 0 := by
  classical
  unfold periodicHypercubicSpecialUnitarySparseActiveTVInfluence
  by_cases hActive :
      source ∈
        periodicHypercubicActiveNeighbors
          (PeriodicHypercubicEvenSideLength H) target
  · exact False.elim
      (hNotLocal
        (periodicHypercubicEvenPlaquetteLocal_of_mem_activeNeighbors_current
          H target source hActive))
  · simp [hActive]

/-- Equivalently, every nonzero current sparse influence edge is an actual
one-plaquette-local edge. -/
theorem periodicHypercubicEvenPlaquetteLocal_of_sparseActiveTVInfluence_ne_zero
    (H : ℕ)
    (beta : ℝ)
    (target source : PeriodicHypercubicEvenEdge H)
    (hNe :
      periodicHypercubicSpecialUnitarySparseActiveTVInfluence
        (PeriodicHypercubicEvenSideLength H) beta target source ≠ 0) :
    periodicHypercubicEvenPlaquetteLocal H target source := by
  by_contra hNotLocal
  exact hNe
    (periodicHypercubicEvenSpecialUnitarySparseActiveTVInfluence_eq_zero_of_not_plaquetteLocal
      H beta target source hNotLocal)

/-- Two-step support separation excludes every direct current sparse influence
from one support to the other. -/
theorem periodicHypercubicEvenSparseActiveTVInfluence_cross_eq_zero_of_supportsSeparatedBy_two
    (H : ℕ)
    (beta : ℝ)
    (S T : Finset (PeriodicHypercubicEvenEdge H))
    (hsep : periodicHypercubicEvenSupportsPlaquetteLocalSeparatedBy H 2 S T)
    (target : PeriodicHypercubicEvenEdge H)
    (htarget : target ∈ S)
    (source : PeriodicHypercubicEvenEdge H)
    (hsource : source ∈ T) :
    periodicHypercubicSpecialUnitarySparseActiveTVInfluence
      (PeriodicHypercubicEvenSideLength H) beta target source = 0 := by
  apply
    periodicHypercubicEvenSpecialUnitarySparseActiveTVInfluence_eq_zero_of_not_plaquetteLocal
  intro hlocal
  exact
    hsep 1 (by norm_num) target htarget source hsource
      (periodicHypercubicEvenPlaquetteLocalPath_one H hlocal)

/-- Positive physical midpoint separation plus the explicit same-root scaling
hypotheses eventually remove every direct sparse conditional-TV influence
between the literal reflected-left and translated-right midpoint supports.
The coupling sequence is arbitrary here: this conclusion uses only locality,
not a small-coupling threshold. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointSupports_eventually_sparseActiveTVInfluence_cross_eq_zero_of_scaling
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
    (beta : ℕ → ℝ) :
    ∀ᶠ n : ℕ in atTop,
      ∀ target : PeriodicHypercubicEvenEdge (H n),
        target ∈
          periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftReflectedSupport
            (H n) latticeSpacing n J →
        ∀ source : PeriodicHypercubicEvenEdge (H n),
          source ∈
            periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightSupport
              (H n) latticeSpacing n J r →
          periodicHypercubicSpecialUnitarySparseActiveTVInfluence
            (PeriodicHypercubicEvenSideLength (H n)) (beta n)
            target source = 0 := by
  have hsep :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointSupports_eventually_plaquetteLocalSeparatedBy_of_scaling
      H latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero hreach
      J hJ r hr 2
  filter_upwards [hsep] with n hsep_n
  intro target htarget source hsource
  exact
    periodicHypercubicEvenSparseActiveTVInfluence_cross_eq_zero_of_supportsSeparatedBy_two
      (H n) (beta n)
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftReflectedSupport
        (H n) latticeSpacing n J)
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightSupport
        (H n) latticeSpacing n J r)
      hsep_n target htarget source hsource

/-- On a positive even half-extent, the current generic compact `SU(N)`
shared-plaquette influence also vanishes on every non-plaquette-local pair. -/
theorem periodicHypercubicEvenSpecialUnitary_sharedPlaquetteInfluence_eq_zero_of_not_plaquetteLocal_current
    (H N : ℕ)
    (hH : 0 < H)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hBeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEvenEdge H)
    (hNotLocal : ¬ periodicHypercubicEvenPlaquetteLocal H target source) :
    specialUnitaryCompactOrientedSharedPlaquetteInfluence
        (periodicHypercubicFiniteOrientedGeometry
          (PeriodicHypercubicEvenSideLength H))
        N hN beta hBeta target source = 0 := by
  have hn : 3 ≤ PeriodicHypercubicEvenSideLength H := by
    simp [PeriodicHypercubicEvenSideLength]
    omega
  rw [periodicHypercubicSpecialUnitary_sharedPlaquetteInfluence_eq_sparseActiveTVInfluence_current
    (PeriodicHypercubicEvenSideLength H) N hn hN beta hBeta target source]
  exact
    periodicHypercubicEvenSpecialUnitarySparseActiveTVInfluence_eq_zero_of_not_plaquetteLocal
      H beta target source hNotLocal

/-- Therefore the influence field of the current compact `SU(N)` Dobrushin
matrix data, when it is constructible under the explicit finite-volume
threshold, has no edge outside the actual Wilson-plaquette-local graph. -/
theorem periodicHypercubicEvenSpecialUnitary_sparseDobrushinMatrixData_influence_eq_zero_of_not_plaquetteLocal
    (H N : ℕ)
    (hH : 0 < H)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hBeta : 0 ≤ beta)
    (hThreshold :
      18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta < 1)
    (target source : PeriodicHypercubicEvenEdge H)
    (hNotLocal : ¬ periodicHypercubicEvenPlaquetteLocal H target source) :
    (periodicHypercubicSpecialUnitary_sparseDobrushinMatrixData_of_threshold
      (PeriodicHypercubicEvenSideLength H) N
      (by
        simp [PeriodicHypercubicEvenSideLength]
        omega)
      hN beta hBeta hThreshold).influence target source = 0 := by
  change
    specialUnitaryCompactOrientedSharedPlaquetteInfluence
        (periodicHypercubicFiniteOrientedGeometry
          (PeriodicHypercubicEvenSideLength H))
        N hN beta hBeta target source = 0
  exact
    periodicHypercubicEvenSpecialUnitary_sharedPlaquetteInfluence_eq_zero_of_not_plaquetteLocal_current
      H N hH hN beta hBeta target source hNotLocal

/-- In particular, two-step actual support separation kills every direct
current-Dobrushin influence between the two supports. -/
theorem periodicHypercubicEvenSpecialUnitary_sparseDobrushinMatrixData_cross_influence_eq_zero_of_supportsSeparatedBy_two
    (H N : ℕ)
    (hH : 0 < H)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hBeta : 0 ≤ beta)
    (hThreshold :
      18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta < 1)
    (S T : Finset (PeriodicHypercubicEvenEdge H))
    (hsep : periodicHypercubicEvenSupportsPlaquetteLocalSeparatedBy H 2 S T)
    (target : PeriodicHypercubicEvenEdge H)
    (htarget : target ∈ S)
    (source : PeriodicHypercubicEvenEdge H)
    (hsource : source ∈ T) :
    (periodicHypercubicSpecialUnitary_sparseDobrushinMatrixData_of_threshold
      (PeriodicHypercubicEvenSideLength H) N
      (by
        simp [PeriodicHypercubicEvenSideLength]
        omega)
      hN beta hBeta hThreshold).influence target source = 0 := by
  apply
    periodicHypercubicEvenSpecialUnitary_sparseDobrushinMatrixData_influence_eq_zero_of_not_plaquetteLocal
      H N hH hN beta hBeta hThreshold target source
  intro hlocal
  exact
    hsep 1 (by norm_num) target htarget source hsource
      (periodicHypercubicEvenPlaquetteLocalPath_one H hlocal)

end

end MathlibAnalytic
end MGAP4D
