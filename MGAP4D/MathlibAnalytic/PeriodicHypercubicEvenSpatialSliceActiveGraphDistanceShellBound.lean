import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpatialSliceActiveGraphFiniteDistance
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance spatialSliceActiveGraphDistanceShellLinkFintype
    (H : Nat) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- In the connected spatial active graph, distance zero characterizes the
selected spatial link. -/
theorem periodicHypercubicEvenSpatialSliceActiveGraphDistance_eq_zero_iff
    (H : Nat)
    (selected p : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpatialSliceActiveGraphDistance H selected p = 0 ↔
      p = selected := by
  change (periodicHypercubicEvenSpatialSliceActiveGraph H).dist selected p = 0 ↔ _
  simpa [eq_comm] using
    (periodicHypercubicEvenSpatialSliceActiveGraph_connected H).dist_eq_zero_iff
      (u := selected) (v := p)

/-- A spatial link at graph distance m+1 admits an adjacent predecessor at
distance m, obtained from a shortest path. -/
theorem periodicHypercubicEvenSpatialSliceActiveGraphDistance_exists_predecessor
    (H : Nat)
    (selected q : PeriodicHypercubicEvenSpatialSliceLink H)
    (m : Nat)
    (hq :
      periodicHypercubicEvenSpatialSliceActiveGraphDistance H selected q =
        m + 1) :
    ∃ r : PeriodicHypercubicEvenSpatialSliceLink H,
      periodicHypercubicEvenSpatialSliceActiveGraphDistance H selected r = m ∧
        (periodicHypercubicEvenSpatialSliceActiveGraph H).Adj r q := by
  let G := periodicHypercubicEvenSpatialSliceActiveGraph H
  obtain ⟨w, _hwPath, hwLength⟩ :=
    (periodicHypercubicEvenSpatialSliceActiveGraph_connected H selected q).exists_path_of_dist
  change G.dist selected q = m + 1 at hq
  have hLength : w.length = m + 1 := hwLength.trans hq
  let r := w.getVert m
  have hm_lt : m < w.length := by omega
  have hAdjRaw : G.Adj (w.getVert m) (w.getVert (m + 1)) := by
    exact w.adj_getVert_succ hm_lt
  have hEnd : w.getVert (m + 1) = q := by
    rw [← hLength]
    simp
  have hAdj : G.Adj r q := by
    exact hEnd ▸ hAdjRaw
  have hSubwalk :=
    SimpleGraph.length_eq_dist_of_subwalk hwLength (w.isSubwalk_take m)
  have hTakeLength : (w.take m).length = m := by
    simp [hLength]
  have hDistance : G.dist selected r = m := by
    rw [hTakeLength] at hSubwalk
    exact hSubwalk.symm
  exact ⟨r, hDistance, hAdj⟩

/-- The zero graph-distance shell is exactly the singleton selected link. -/
theorem periodicHypercubicEvenSpatialSliceActiveGraphDistanceShell_zero
    (H : Nat)
    (selected : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpatialSliceActiveGraphDistanceShell H selected 0 =
      {selected} := by
  classical
  apply Finset.ext
  intro p
  simp [periodicHypercubicEvenSpatialSliceActiveGraphDistance_eq_zero_iff
    H selected p]

/-- Every link in the next graph-distance shell lies in the union of the
canonical active-neighbor rows of links in the current shell. -/
theorem periodicHypercubicEvenSpatialSliceActiveGraphDistanceShell_succ_subset_neighbors
    (H : Nat)
    (selected : PeriodicHypercubicEvenSpatialSliceLink H)
    (m : Nat) :
    periodicHypercubicEvenSpatialSliceActiveGraphDistanceShell H selected (m + 1) ⊆
      (periodicHypercubicEvenSpatialSliceActiveGraphDistanceShell H selected m).biUnion
        (periodicHypercubicEvenSpatialSliceActiveGraphAdjFinset H) := by
  classical
  intro q hq
  have hDistance :
      periodicHypercubicEvenSpatialSliceActiveGraphDistance H selected q =
        m + 1 :=
    (periodicHypercubicEvenSpatialSliceActiveGraph_mem_distanceShell_iff
      H selected q (m + 1)).mp hq
  obtain ⟨r, hrDistance, hrq⟩ :=
    periodicHypercubicEvenSpatialSliceActiveGraphDistance_exists_predecessor
      H selected q m hDistance
  apply Finset.mem_biUnion.mpr
  refine ⟨r, ?_, ?_⟩
  · exact
      (periodicHypercubicEvenSpatialSliceActiveGraph_mem_distanceShell_iff
        H selected r m).mpr hrDistance
  · exact
      (periodicHypercubicEvenSpatialSliceActiveGraph_mem_adjFinset_iff
        H r q).mpr hrq

/-- One graph-shell expansion multiplies cardinality by at most the uniform
spatial active-neighbor bound 18. -/
theorem periodicHypercubicEvenSpatialSliceActiveGraphDistanceShell_succ_card_le
    (H : Nat)
    (selected : PeriodicHypercubicEvenSpatialSliceLink H)
    (m : Nat) :
    (periodicHypercubicEvenSpatialSliceActiveGraphDistanceShell
      H selected (m + 1)).card ≤
      (periodicHypercubicEvenSpatialSliceActiveGraphDistanceShell
        H selected m).card * 18 := by
  classical
  let shell :=
    periodicHypercubicEvenSpatialSliceActiveGraphDistanceShell H selected m
  calc
    (periodicHypercubicEvenSpatialSliceActiveGraphDistanceShell
        H selected (m + 1)).card ≤
        (shell.biUnion
          (periodicHypercubicEvenSpatialSliceActiveGraphAdjFinset H)).card :=
      Finset.card_le_card
        (periodicHypercubicEvenSpatialSliceActiveGraphDistanceShell_succ_subset_neighbors
          H selected m)
    _ ≤ ∑ p ∈ shell,
          (periodicHypercubicEvenSpatialSliceActiveGraphAdjFinset H p).card :=
      finset_card_biUnion_le_sum_card shell
        (periodicHypercubicEvenSpatialSliceActiveGraphAdjFinset H)
    _ ≤ ∑ _p ∈ shell, 18 := by
      apply Finset.sum_le_sum
      intro p _hp
      exact
        periodicHypercubicEvenSpatialSliceActiveGraph_adjFinset_card_le_eighteen
          H p
    _ = shell.card * 18 := by simp

/-- Coarse graph-distance shells grow at most exponentially with base 18,
uniformly in the periodic volume and selected link. This is a graph-degree
bound, not the sharper polynomial base-L1 shell estimate. -/
theorem periodicHypercubicEvenSpatialSliceActiveGraphDistanceShell_card_le_pow_eighteen
    (H : Nat)
    (selected : PeriodicHypercubicEvenSpatialSliceLink H)
    (m : Nat) :
    (periodicHypercubicEvenSpatialSliceActiveGraphDistanceShell H selected m).card ≤
      18 ^ m := by
  induction m with
  | zero =>
      rw [periodicHypercubicEvenSpatialSliceActiveGraphDistanceShell_zero
        H selected]
      simp
  | succ m ih =>
      calc
        (periodicHypercubicEvenSpatialSliceActiveGraphDistanceShell
            H selected (m + 1)).card ≤
            (periodicHypercubicEvenSpatialSliceActiveGraphDistanceShell
              H selected m).card * 18 :=
          periodicHypercubicEvenSpatialSliceActiveGraphDistanceShell_succ_card_le
            H selected m
        _ ≤ 18 ^ m * 18 := Nat.mul_le_mul_right 18 ih
        _ = 18 ^ (m + 1) := by rw [pow_succ]

/-- Real-valued form of the coarse 18^m graph-distance shell bound. -/
theorem periodicHypercubicEvenSpatialSliceActiveGraphDistanceShell_card_real_le
    (H : Nat)
    (selected : PeriodicHypercubicEvenSpatialSliceLink H)
    (m : Nat) :
    ((periodicHypercubicEvenSpatialSliceActiveGraphDistanceShell
      H selected m).card : Real) ≤
      (18 : Real) ^ m := by
  exact_mod_cast
    periodicHypercubicEvenSpatialSliceActiveGraphDistanceShell_card_le_pow_eighteen
      H selected m

end

end MathlibAnalytic
end MGAP4D
