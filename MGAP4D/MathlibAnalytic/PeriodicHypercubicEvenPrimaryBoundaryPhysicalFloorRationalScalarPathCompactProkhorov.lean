import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalSlotTemporalReach
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Tactic

/-!
# Compact-support Prokhorov limit for the one-sided primary scalar path laws

After scalarization by the canonical primary spatial plaquette normalized trace,
the finite path carrier is the fixed space `ℚ → ℝ`.  More is true: every scalar
coordinate lies in `[-1,1]`.  Hence every finite scalar path law is supported on
the same compact Tychonoff cube `[-1,1]^ℚ`.

This file uses that exact common support to prove tightness and extract a weakly
convergent subsequence by Mathlib's Prokhorov theorem.  No cross-scale equality
of edge-valued carriers, coercive-moment premise, continuum positivity premise,
physical-volume identity, or additional model hypothesis is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Set

noncomputable section

/-- The canonical primary-boundary scalar plaquette coordinate always lies in
`[-1,1]`, because it is exactly a normalized real `SU(N)` trace. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePrimaryBoundary_mem_Icc
    (H N : ℕ) (hN : 0 < N)
    (u : PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePrimaryBoundary H N u ∈
      Set.Icc (-1 : ℝ) 1 := by
  rw [periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePrimaryBoundary_eq]
  exact normalizedSpecialUnitaryRealTrace_mem_Icc hN _

/-- Common fixed compact carrier containing every scalar rational path produced
at every lattice scale. -/
def periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathCompactCube :
    Set (ℚ → ℝ) :=
  {x | ∀ q, x q ∈ Set.Icc (-1 : ℝ) 1}

/-- Tychonoff compactness of the common path cube. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathCompactCube_isCompact :
    IsCompact periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathCompactCube := by
  unfold periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathCompactCube
  exact isCompact_pi_infinite (fun _ => isCompact_Icc)

/-- Every scalarization of a completed primary edge path lands in the common
compact cube, independently of the half extent. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath_mem_compactCube
    (H N : ℕ) (hN : 0 < N)
    (x : ℚ →
      (PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H →
        Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath H N x ∈
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathCompactCube := by
  intro q
  exact
    periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePrimaryBoundary_mem_Icc
      H N hN (x q)

/-- The actual finite same-root scalar path measure assigns zero mass to the
complement of the common compact cube. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure_compactCube_compl_eq_zero
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure
        H N hN beta hbeta latticeSpacing n
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathCompactCubeᶜ) = 0 := by
  unfold periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure
  rw [Measure.map_apply_of_aemeasurable
    (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath_measurable
      H N).aemeasurable
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathCompactCube_isCompact.measurableSet.compl]
  have hpre :
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath H N ⁻¹'
          periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathCompactCubeᶜ = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro x hx
    exact hx
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath_mem_compactCube
        H N hN x)
  rw [hpre, measure_empty]

/-- The probability-measure packaging has the same exact compact support. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure_compactCube_compl_eq_zero
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ) :
    ((periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure
        H N hN beta hbeta latticeSpacing n : ProbabilityMeasure (ℚ → ℝ)) :
      Measure (ℚ → ℝ))
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathCompactCubeᶜ) = 0 := by
  rw [periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure_toMeasure]
  exact
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure_compactCube_compl_eq_zero
      H N hN beta hbeta latticeSpacing n

/-- The sequence of actual finite scalar path probability laws on the fixed
carrier. -/
def periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasureSet
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ) :
    Set (ProbabilityMeasure (ℚ → ℝ)) :=
  Set.range fun n =>
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure
      (H n) N hN (beta n) (hbeta n) latticeSpacing n

/-- Common compact support gives uniform tightness of the entire finite scalar
path-law family, with no moment estimate. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasureSet_isTight
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ) :
    IsTightMeasureSet
      {((μ : ProbabilityMeasure (ℚ → ℝ)) : Measure (ℚ → ℝ)) |
        μ ∈ periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasureSet
          H N hN beta hbeta latticeSpacing} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  refine ⟨
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathCompactCube,
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathCompactCube_isCompact,
    ?_⟩
  intro μ hμ
  rcases hμ with ⟨ν, hν, rfl⟩
  rcases hν with ⟨n, rfl⟩
  rw [periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure_compactCube_compl_eq_zero]
  exact bot_le

/-- A Prokhorov subsequential limit extracted directly from the new same-root
one-sided primary scalar path laws. -/
structure PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ) where
  continuumMeasure : ProbabilityMeasure (ℚ → ℝ)
  subsequence : ℕ → ℕ
  subsequence_strictMono : StrictMono subsequence
  weakConvergence :
    Tendsto
      (fun n =>
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure
          (H (subsequence n)) N hN
          (beta (subsequence n)) (hbeta (subsequence n))
          latticeSpacing (subsequence n))
      atTop
      (nhds continuumMeasure)

/-- Mathlib Prokhorov compactness supplies an actual weakly convergent
subsequence of the same finite Wilson-derived scalar laws. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath_prokhorovSubsequence_exists
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ) :
    Nonempty
      (PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
        H N hN beta hbeta latticeSpacing) := by
  let μseq : ℕ → ProbabilityMeasure (ℚ → ℝ) := fun n =>
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure
      (H n) N hN (beta n) (hbeta n) latticeSpacing n
  let S : Set (ProbabilityMeasure (ℚ → ℝ)) := Set.range μseq
  have hTight :
      IsTightMeasureSet
        {((μ : ProbabilityMeasure (ℚ → ℝ)) : Measure (ℚ → ℝ)) | μ ∈ S} := by
    simpa [S, μseq,
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasureSet] using
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasureSet_isTight
        H N hN beta hbeta latticeSpacing
  have hCompact : IsCompact (closure S) :=
    isCompact_closure_of_isTightMeasureSet hTight
  obtain ⟨μlim, _hmem, subsequence, hmono, hconv⟩ :=
    hCompact.isSeqCompact
      (fun n => subset_closure (Set.mem_range_self n : μseq n ∈ S))
  refine ⟨{
    continuumMeasure := μlim
    subsequence := subsequence
    subsequence_strictMono := hmono
    weakConvergence := ?_ }⟩
  simpa [μseq] using hconv

end

end MathlibAnalytic
end MGAP4D
