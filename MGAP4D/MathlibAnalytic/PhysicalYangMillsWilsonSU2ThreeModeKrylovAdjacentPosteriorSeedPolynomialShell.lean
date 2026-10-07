import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPosteriorSeedCovarianceDecay
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceTwoStepTerminalSpatialBaseL1PolynomialShellBound
import MGAP4D.MathlibAnalytic.CubicSpatialShellGeometricSummability
import Mathlib.Tactic

/-!
# Volume-independent polynomial shells for primary-plaquette seed distance

The primary seed distance is the minimum of the four periodic base-L1 distances
to the physical links of the canonical primary spatial plaquette. Therefore an
exact seed-distance shell at radius r is contained in the union of the four
ordinary base-L1 shells at radius r, one around each seed link.

The existing three-dimensional torus geometry theorem bounds each ordinary
spatial-link shell by

  3 * (2*r + 1)^3.

Hence the exact primary-seed shell has the volume-independent bound

  12 * (2*r + 1)^3,

or equivalently four times the existing real cubic shell majorant. Combining
this with the existing polynomial-times-geometric summability theorem shows
that any geometric profile q^r with 0 <= q < 1 is summable against the seed
shell majorant. In particular there is no artificial condition 18*q < 1.

This is a geometry/summability result. It does not identify the actual frozen
centered source-coordinate L2 norm with a covariance sum and it does not remove
the retained output/half-density drift.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance p3PrimarySeedPolynomialShellSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

private theorem nat_min_four_eq_level
    (a b c d r : ℕ)
    (h : min a (min b (min c d)) = r) :
    a = r ∨ b = r ∨ c = r ∨ d = r := by
  by_cases h0 : a ≤ min b (min c d)
  · left
    simpa [min_eq_left h0] using h
  · have h0' : min b (min c d) ≤ a := le_of_not_ge h0
    have hrest : min b (min c d) = r := by
      simpa [min_eq_right h0'] using h
    by_cases h1 : b ≤ min c d
    · right
      left
      simpa [min_eq_left h1] using hrest
    · have h1' : min c d ≤ b := le_of_not_ge h1
      have hrest' : min c d = r := by
        simpa [min_eq_right h1'] using hrest
      by_cases h2 : c ≤ d
      · right
        right
        left
        simpa [min_eq_left h2] using hrest'
      · have h2' : d ≤ c := le_of_not_ge h2
        right
        right
        right
        simpa [min_eq_right h2'] using hrest'

/-- Exact shell of spatial links at fixed distance from the four-link canonical
primary-plaquette seed. -/
noncomputable def physicalYangMillsSU2PrimaryPlaquetteSeedDistanceShell
    (H r : ℕ) :
    Finset (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Finset.univ.filter
    (fun source =>
      physicalYangMillsSU2PrimaryPlaquetteSeedDistance H source = r)

@[simp] theorem physicalYangMillsSU2PrimaryPlaquette_mem_seedDistanceShell
    (H r : ℕ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    source ∈ physicalYangMillsSU2PrimaryPlaquetteSeedDistanceShell H r ↔
      physicalYangMillsSU2PrimaryPlaquetteSeedDistance H source = r := by
  simp [physicalYangMillsSU2PrimaryPlaquetteSeedDistanceShell]

/-- The exact seed-distance shell is contained in the union of the four exact
base-L1 shells centered at the seed links. -/
theorem physicalYangMillsSU2PrimaryPlaquetteSeedDistanceShell_subset_fourBaseL1Shells
    (H r : ℕ) :
    physicalYangMillsSU2PrimaryPlaquetteSeedDistanceShell H r ⊆
      (Finset.univ : Finset (Fin 4)).biUnion
        (fun k =>
          Finset.univ.filter
            (fun source : PeriodicHypercubicEvenSpatialSliceLink H =>
              periodicHypercubicEdgeBaseL1Distance
                  (PeriodicHypercubicEvenSideLength H)
                  (periodicHypercubicEvenSpatialSliceLinkEmbedding H source)
                  (periodicHypercubicEvenSpatialSliceLinkEmbedding H
                    (physicalYangMillsSU2PrimaryPlaquetteSeedLink H k)) = r)) := by
  classical
  intro source hSource
  have hSeed :
      physicalYangMillsSU2PrimaryPlaquetteSeedDistance H source = r :=
    (physicalYangMillsSU2PrimaryPlaquette_mem_seedDistanceShell H r source).mp hSource
  unfold physicalYangMillsSU2PrimaryPlaquetteSeedDistance at hSeed
  rw [
    ← physicalYangMillsSU2PrimaryPlaquetteSeedLinkBaseDistance_symm H source 0,
    ← physicalYangMillsSU2PrimaryPlaquetteSeedLinkBaseDistance_symm H source 1,
    ← physicalYangMillsSU2PrimaryPlaquetteSeedLinkBaseDistance_symm H source 2,
    ← physicalYangMillsSU2PrimaryPlaquetteSeedLinkBaseDistance_symm H source 3
  ] at hSeed
  rcases nat_min_four_eq_level _ _ _ _ _ hSeed with h0 | h1 | h2 | h3
  · refine Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ _, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0⟩
  · refine Finset.mem_biUnion.mpr ⟨1, Finset.mem_univ _, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩
  · refine Finset.mem_biUnion.mpr ⟨2, Finset.mem_univ _, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩
  · refine Finset.mem_biUnion.mpr ⟨3, Finset.mem_univ _, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h3⟩

/-- Volume-independent shell cardinality:
four seed links times the existing three-dimensional link shell bound. -/
theorem physicalYangMillsSU2PrimaryPlaquetteSeedDistanceShell_card_le_polynomial
    (H r : ℕ) :
    (physicalYangMillsSU2PrimaryPlaquetteSeedDistanceShell H r).card ≤
      12 * (2 * r + 1) ^ 3 := by
  classical
  let baseShell : Fin 4 →
      Finset (PeriodicHypercubicEvenSpatialSliceLink H) := fun k =>
    Finset.univ.filter
      (fun source =>
        periodicHypercubicEdgeBaseL1Distance
            (PeriodicHypercubicEvenSideLength H)
            (periodicHypercubicEvenSpatialSliceLinkEmbedding H source)
            (periodicHypercubicEvenSpatialSliceLinkEmbedding H
              (physicalYangMillsSU2PrimaryPlaquetteSeedLink H k)) = r)
  have hSubset :
      physicalYangMillsSU2PrimaryPlaquetteSeedDistanceShell H r ⊆
        (Finset.univ : Finset (Fin 4)).biUnion baseShell := by
    simpa [baseShell] using
      physicalYangMillsSU2PrimaryPlaquetteSeedDistanceShell_subset_fourBaseL1Shells
        H r
  have hUnion :
      ((Finset.univ : Finset (Fin 4)).biUnion baseShell).card ≤
        ∑ k ∈ (Finset.univ : Finset (Fin 4)), (baseShell k).card :=
    finset_card_biUnion_le_sum_card
      (Finset.univ : Finset (Fin 4)) baseShell
  have hEach :
      ∀ k : Fin 4, (baseShell k).card ≤ 3 * (2 * r + 1) ^ 3 := by
    intro k
    simpa [baseShell] using
      periodicHypercubicEvenSpatialSliceBaseL1Shell_card_le_polynomial
        H (physicalYangMillsSU2PrimaryPlaquetteSeedLink H k) r
  calc
    (physicalYangMillsSU2PrimaryPlaquetteSeedDistanceShell H r).card ≤
        ((Finset.univ : Finset (Fin 4)).biUnion baseShell).card :=
      Finset.card_le_card hSubset
    _ ≤ ∑ k ∈ (Finset.univ : Finset (Fin 4)), (baseShell k).card :=
      hUnion
    _ ≤ ∑ _k ∈ (Finset.univ : Finset (Fin 4)),
        3 * (2 * r + 1) ^ 3 := by
      apply Finset.sum_le_sum
      intro k _hk
      exact hEach k
    _ = 12 * (2 * r + 1) ^ 3 := by
      simp
      ring

/-- Real-valued majorant for the primary-seed shell. -/
def physicalYangMillsSU2PrimaryPlaquetteSeedDistanceShellMajorant
    (r : ℕ) : ℝ :=
  4 * cubicSpatialShellMajorant r

theorem physicalYangMillsSU2PrimaryPlaquetteSeedDistanceShellMajorant_nonneg
    (r : ℕ) :
    0 ≤ physicalYangMillsSU2PrimaryPlaquetteSeedDistanceShellMajorant r := by
  unfold physicalYangMillsSU2PrimaryPlaquetteSeedDistanceShellMajorant
  exact mul_nonneg (by norm_num) (cubicSpatialShellMajorant_nonneg r)

/-- Casted shell-cardinality bound in the form consumed by real-valued
geometric summability. -/
theorem physicalYangMillsSU2PrimaryPlaquetteSeedDistanceShell_card_real_le_majorant
    (H r : ℕ) :
    ((physicalYangMillsSU2PrimaryPlaquetteSeedDistanceShell H r).card : ℝ) ≤
      physicalYangMillsSU2PrimaryPlaquetteSeedDistanceShellMajorant r := by
  have hNat :=
    physicalYangMillsSU2PrimaryPlaquetteSeedDistanceShell_card_le_polynomial H r
  have hReal :
      ((physicalYangMillsSU2PrimaryPlaquetteSeedDistanceShell H r).card : ℝ) ≤
        ((12 * (2 * r + 1) ^ 3 : ℕ) : ℝ) := by
    exact_mod_cast hNat
  unfold physicalYangMillsSU2PrimaryPlaquetteSeedDistanceShellMajorant
    cubicSpatialShellMajorant
  calc
    ((physicalYangMillsSU2PrimaryPlaquetteSeedDistanceShell H r).card : ℝ) ≤
        ((12 * (2 * r + 1) ^ 3 : ℕ) : ℝ) := hReal
    _ = 4 * (3 * (2 * (r : ℝ) + 1) ^ 3) := by
      push_cast
      ring

/-- Polynomial seed shells are summable against every genuine geometric
profile. The constant C is arbitrary and can later absorb the covariance
prefactor and the four seed observables. -/
theorem summable_physicalYangMillsSU2PrimaryPlaquetteSeedDistanceShellMajorant_mul_geometric
    (C q : ℝ)
    (hqNonneg : 0 ≤ q)
    (hqLtOne : q < 1) :
    Summable (fun r : ℕ =>
      physicalYangMillsSU2PrimaryPlaquetteSeedDistanceShellMajorant r *
        (C * q ^ r)) := by
  have h :=
    summable_cubicSpatialShellMajorant_mul_geometric_of_nonneg_lt_one
      (4 * C) q hqNonneg hqLtOne
  apply h.congr
  intro r
  unfold physicalYangMillsSU2PrimaryPlaquetteSeedDistanceShellMajorant
  ring

end

end MathlibAnalytic
end MGAP4D
