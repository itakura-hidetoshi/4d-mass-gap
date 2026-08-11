import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenHalfSectorEdgeSupport
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Exact incidence pattern at the primary reflection-fixed slice. -/
def periodicHypercubicEvenPositiveBoundaryTemporalPrimaryEdgePattern
    (H : ℕ) (p : PeriodicHypercubicEvenPlaquette H) : Prop :=
  (p.1 0).val = 0 ∧
    (periodicHypercubicEvenEdgeOrbitPartition H).side
        (periodicHypercubicBoundaryStep
          (PeriodicHypercubicEvenSideLength H) p 0).edge =
      ReflectionEdgeSide.positive ∧
    (periodicHypercubicEvenEdgeOrbitPartition H).side
        (periodicHypercubicBoundaryStep
          (PeriodicHypercubicEvenSideLength H) p 1).edge =
      ReflectionEdgeSide.positive ∧
    (periodicHypercubicEvenEdgeOrbitPartition H).side
        (periodicHypercubicBoundaryStep
          (PeriodicHypercubicEvenSideLength H) p 2).edge =
      ReflectionEdgeSide.positive ∧
    (periodicHypercubicEvenEdgeOrbitPartition H).side
        (periodicHypercubicBoundaryStep
          (PeriodicHypercubicEvenSideLength H) p 3).edge =
      ReflectionEdgeSide.fixed

/-- Exact incidence pattern at the antipodal-adjacent positive slice. -/
def periodicHypercubicEvenPositiveBoundaryTemporalAntipodalEdgePattern
    (H : ℕ) (p : PeriodicHypercubicEvenPlaquette H) : Prop :=
  (p.1 0).val = H ∧
    (periodicHypercubicEvenEdgeOrbitPartition H).side
        (periodicHypercubicBoundaryStep
          (PeriodicHypercubicEvenSideLength H) p 0).edge =
      ReflectionEdgeSide.positive ∧
    (periodicHypercubicEvenEdgeOrbitPartition H).side
        (periodicHypercubicBoundaryStep
          (PeriodicHypercubicEvenSideLength H) p 1).edge =
      ReflectionEdgeSide.fixed ∧
    (periodicHypercubicEvenEdgeOrbitPartition H).side
        (periodicHypercubicBoundaryStep
          (PeriodicHypercubicEvenSideLength H) p 2).edge =
      ReflectionEdgeSide.positive ∧
    (periodicHypercubicEvenEdgeOrbitPartition H).side
        (periodicHypercubicBoundaryStep
          (PeriodicHypercubicEvenSideLength H) p 3).edge =
      ReflectionEdgeSide.positive

/-- The two exact positive-boundary temporal incidence patterns. -/
def periodicHypercubicEvenPositiveBoundaryTemporalExactEdgePattern
    (H : ℕ) (p : PeriodicHypercubicEvenPlaquette H) : Prop :=
  periodicHypercubicEvenPositiveBoundaryTemporalPrimaryEdgePattern H p ∨
    periodicHypercubicEvenPositiveBoundaryTemporalAntipodalEdgePattern H p

/-- For a nondegenerate positive half-torus (`H > 0`), a temporal plaquette
adjacent to a reflection-fixed slice has exactly one fixed spatial boundary
incidence and three positive incidences.

At the primary fixed slice (`t = 0`) the fixed incidence is step `3`; at the
antipodal-adjacent positive slice (`t = H`) it is step `1`.  The two temporal
incidences (`0` and `2`) are always positive.  This exact four-edge pattern is
the combinatorial skeleton needed to split the plaquette holonomy into one
shared-boundary leg and a three-edge positive-half path. -/
theorem periodicHypercubicEvenPositiveBoundaryTemporalPlaquette_exact_edge_pattern
    {H : ℕ}
    (hH : 0 < H)
    (p : PeriodicHypercubicEvenPlaquette H)
    (hp : periodicHypercubicEvenPositiveBoundaryTemporalPlaquette p) :
    periodicHypercubicEvenPositiveBoundaryTemporalExactEdgePattern H p := by
  unfold periodicHypercubicEvenPositiveBoundaryTemporalExactEdgePattern
  have htime := hp.1
  have hmu :=
    (periodicHypercubicEvenPlaquetteHasTimeDirection_iff_firstAxis_zero p).1 htime
  have hnu : periodicHypercubicPlaquetteSecondAxis p ≠ 0 :=
    periodicHypercubicPlaquetteSecondAxis_ne_zero p
  have hstep0 :
      (periodicHypercubicEvenEdgeOrbitPartition H).side
          (periodicHypercubicBoundaryStep
            (PeriodicHypercubicEvenSideLength H) p 0).edge =
        ReflectionEdgeSide.positive := by
    change periodicHypercubicEvenEdgeSide H
      (p.1, periodicHypercubicPlaquetteFirstAxis p) =
        ReflectionEdgeSide.positive
    rw [hmu]
    exact periodicHypercubicEvenEdgeSide_time_eq_positive_of_val_le
      H p.1 (by rcases hp.2 with h | h <;> omega)
  have hstep2 :
      (periodicHypercubicEvenEdgeOrbitPartition H).side
          (periodicHypercubicBoundaryStep
            (PeriodicHypercubicEvenSideLength H) p 2).edge =
        ReflectionEdgeSide.positive := by
    change periodicHypercubicEvenEdgeSide H
      (periodicHypercubicEvenPlaquetteCorner01 p,
        periodicHypercubicPlaquetteFirstAxis p) =
        ReflectionEdgeSide.positive
    rw [hmu]
    apply periodicHypercubicEvenEdgeSide_time_eq_positive_of_val_le
    rw [periodicHypercubicEvenPlaquetteCorner01_time_of_hasTimeDirection
      p htime]
    rcases hp.2 with h | h <;> omega
  rcases hp.2 with hbase0 | hbaseH
  · left
    unfold periodicHypercubicEvenPositiveBoundaryTemporalPrimaryEdgePattern
    have hnowrap :
        (p.1 0).val + 1 < PeriodicHypercubicEvenSideLength H := by
      simp only [PeriodicHypercubicEvenSideLength]
      omega
    have hnext := periodicHypercubicEven_val_add_one_of_lt H (p.1 0) hnowrap
    have h10 :
        (periodicHypercubicEvenPlaquetteCorner10 p 0).val = 1 := by
      rw [periodicHypercubicEvenPlaquetteCorner10_time_of_hasTimeDirection
        p htime, hnext, hbase0]
    have hstep1 :
        (periodicHypercubicEvenEdgeOrbitPartition H).side
            (periodicHypercubicBoundaryStep
              (PeriodicHypercubicEvenSideLength H) p 1).edge =
          ReflectionEdgeSide.positive := by
      change periodicHypercubicEvenEdgeSide H
        (periodicHypercubicEvenPlaquetteCorner10 p,
          periodicHypercubicPlaquetteSecondAxis p) =
        ReflectionEdgeSide.positive
      exact periodicHypercubicEvenEdgeSide_spatial_eq_positive_of_val
        H _ hnu (by rw [h10]) (by rw [h10]; omega)
    have hstep3 :
        (periodicHypercubicEvenEdgeOrbitPartition H).side
            (periodicHypercubicBoundaryStep
              (PeriodicHypercubicEvenSideLength H) p 3).edge =
          ReflectionEdgeSide.fixed := by
      change periodicHypercubicEvenEdgeSide H
        (p.1, periodicHypercubicPlaquetteSecondAxis p) =
          ReflectionEdgeSide.fixed
      exact periodicHypercubicEvenEdgeSide_spatial_eq_fixed_of_val_eq_zero
        H _ hnu hbase0
    exact ⟨hbase0, hstep0, hstep1, hstep2, hstep3⟩
  · right
    unfold periodicHypercubicEvenPositiveBoundaryTemporalAntipodalEdgePattern
    have hnowrap :
        (p.1 0).val + 1 < PeriodicHypercubicEvenSideLength H := by
      simp only [PeriodicHypercubicEvenSideLength]
      omega
    have hnext := periodicHypercubicEven_val_add_one_of_lt H (p.1 0) hnowrap
    have h10 :
        (periodicHypercubicEvenPlaquetteCorner10 p 0).val = H + 1 := by
      rw [periodicHypercubicEvenPlaquetteCorner10_time_of_hasTimeDirection
        p htime, hnext, hbaseH]
    have hstep1 :
        (periodicHypercubicEvenEdgeOrbitPartition H).side
            (periodicHypercubicBoundaryStep
              (PeriodicHypercubicEvenSideLength H) p 1).edge =
          ReflectionEdgeSide.fixed := by
      change periodicHypercubicEvenEdgeSide H
        (periodicHypercubicEvenPlaquetteCorner10 p,
          periodicHypercubicPlaquetteSecondAxis p) =
        ReflectionEdgeSide.fixed
      exact periodicHypercubicEvenEdgeSide_spatial_eq_fixed_of_val_eq_half
        H _ hnu h10
    have hbasePos : 1 ≤ (p.1 0).val := by
      omega
    have hbaseLe : (p.1 0).val ≤ H := by
      omega
    have hstep3 :
        (periodicHypercubicEvenEdgeOrbitPartition H).side
            (periodicHypercubicBoundaryStep
              (PeriodicHypercubicEvenSideLength H) p 3).edge =
          ReflectionEdgeSide.positive := by
      change periodicHypercubicEvenEdgeSide H
        (p.1, periodicHypercubicPlaquetteSecondAxis p) =
          ReflectionEdgeSide.positive
      exact periodicHypercubicEvenEdgeSide_spatial_eq_positive_of_val
        H (p.1, periodicHypercubicPlaquetteSecondAxis p) hnu hbasePos hbaseLe
    exact ⟨hbaseH, hstep0, hstep1, hstep2, hstep3⟩

/-- In a nondegenerate positive half-torus, a positive-boundary temporal
plaquette has exactly one fixed incidence among its four signed boundary
steps. -/
theorem periodicHypercubicEvenPositiveBoundaryTemporalPlaquette_existsUnique_fixed_step
    {H : ℕ}
    (hH : 0 < H)
    (p : PeriodicHypercubicEvenPlaquette H)
    (hp : periodicHypercubicEvenPositiveBoundaryTemporalPlaquette p) :
    ∃! k : Fin 4,
      (periodicHypercubicEvenEdgeOrbitPartition H).side
          (periodicHypercubicBoundaryStep
            (PeriodicHypercubicEvenSideLength H) p k).edge =
        ReflectionEdgeSide.fixed := by
  have hpattern :=
    periodicHypercubicEvenPositiveBoundaryTemporalPlaquette_exact_edge_pattern
      hH p hp
  unfold periodicHypercubicEvenPositiveBoundaryTemporalExactEdgePattern at hpattern
  rcases hpattern with hprimary | hantipodal
  · unfold periodicHypercubicEvenPositiveBoundaryTemporalPrimaryEdgePattern at hprimary
    refine ⟨3, hprimary.2.2.2.2, ?_⟩
    intro k hk
    fin_cases k
    · rw [hprimary.2.1] at hk
      cases hk
    · rw [hprimary.2.2.1] at hk
      cases hk
    · rw [hprimary.2.2.2.1] at hk
      cases hk
    · rfl
  · unfold periodicHypercubicEvenPositiveBoundaryTemporalAntipodalEdgePattern at hantipodal
    refine ⟨1, hantipodal.2.2.1, ?_⟩
    intro k hk
    fin_cases k
    · rw [hantipodal.2.1] at hk
      cases hk
    · rfl
    · rw [hantipodal.2.2.2.1] at hk
      cases hk
    · rw [hantipodal.2.2.2.2] at hk
      cases hk

end

end MathlibAnalytic
end MGAP4D
