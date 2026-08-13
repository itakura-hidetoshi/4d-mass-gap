import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryTemporalCompanionOpenPathSection
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPositiveBoundaryTemporalWilsonResidualProduct
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The selected upper spatial edge of every primary companion is based at
positive time `1`. -/
theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionUpperSpatialEdge_source_time_val_one
    (H : ℕ) (k : Fin 4) :
    ((periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionUpperSpatialEdge H k).1 0).val =
      1 := by
  rw [periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionUpperSpatialEdge_eq]
  change
    (periodicHypercubicShift
      (PeriodicHypercubicEvenSideLength H)
      (periodicHypercubicEvenPrimarySpatialPlaquetteEdge H k).1
      (0 : PeriodicHypercubicAxis) 0).val = 1
  rw [periodicHypercubicShift_apply]
  simp only [if_pos rfl]
  have hzero :=
    periodicHypercubicEvenPrimarySpatialPlaquetteEdge_source_time_val_zero H k
  have hnowrap :
      ((periodicHypercubicEvenPrimarySpatialPlaquetteEdge H k).1 0).val + 1 <
        PeriodicHypercubicEvenSideLength H := by
    rw [hzero]
    simp [PeriodicHypercubicEvenSideLength]
  rw [periodicHypercubicEven_val_add_one_of_lt H _ hnowrap, hzero]

private theorem
    periodicHypercubicEvenPrimaryCompanionOpenHalfSection_eq_one_of_direction_zero
    (H : ℕ) (hH : 0 < H)
    {Gauge : Type} [Group Gauge]
    (u : Fin 4 → Gauge)
    (e : (periodicHypercubicEvenEdgeOrbitPartition H).PositiveEdge)
    (hdir : e.1.2 = (0 : PeriodicHypercubicAxis)) :
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfSection
        H hH u e = 1 := by
  unfold periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfSection
  rw [dif_neg]
  rintro ⟨j, hj⟩
  have hval := congrArg Subtype.val hj
  have hdirection := congrArg Prod.snd hval
  apply periodicHypercubicEvenPrimarySpatialPlaquetteEdge_direction_ne_zero H j
  have hz :
      (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionUpperSpatialEdge H j).2 =
        (0 : PeriodicHypercubicAxis) :=
    hdirection.trans hdir
  simpa [
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionUpperSpatialEdge,
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion,
    periodicHypercubicEvenPrimarySpatialEdgeTemporalCompanion] using hz

private theorem
    periodicHypercubicEvenPrimaryResidualStepOne_not_primaryCompanionUpperSpatialRange
    {H : ℕ}
    (hH : 0 < H)
    (p : PeriodicHypercubicEvenPlaquette H)
    (hpResidual :
      p ∈ periodicHypercubicEvenPositiveBoundaryTemporalResidualPlaquettes H)
    (hprimary : periodicHypercubicEvenPositiveBoundaryTemporalPrimaryEdgePattern H p) :
    ¬ ∃ j : Fin 4,
      periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionUpperSpatialEdgeEmbedding
          H hH j =
        (⟨(periodicHypercubicBoundaryStep
            (PeriodicHypercubicEvenSideLength H) p 1).edge,
          hprimary.2.2.1⟩ :
          (periodicHypercubicEvenEdgeOrbitPartition H).PositiveEdge) := by
  rintro ⟨j, hj⟩
  have hval := congrArg Subtype.val hj
  change
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionUpperSpatialEdge H j =
      (periodicHypercubicBoundaryStep
        (PeriodicHypercubicEvenSideLength H) p 1).edge at hval
  rw [periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionUpperSpatialEdge_eq,
    periodicHypercubicBoundaryStep_one] at hval
  have hsource := congrArg Prod.fst hval
  have hdirection := congrArg Prod.snd hval
  rw [show periodicHypercubicPlaquetteFirstAxis p = (0 : PeriodicHypercubicAxis) by
    exact (periodicHypercubicEvenPlaquetteHasTimeDirection_iff_firstAxis_zero p).1
      ((periodicHypercubicEven_mem_positiveBoundaryTemporalPlaquettes p).1
        (Finset.mem_sdiff.mp hpResidual).1).1] at hsource
  have hbase :
      (periodicHypercubicEvenPrimarySpatialPlaquetteEdge H j).1 = p.1 := by
    have hsource' := congrArg
      (fun v => periodicHypercubicUnshift
        (PeriodicHypercubicEvenSideLength H) v (0 : PeriodicHypercubicAxis))
      hsource
    simpa only [periodicHypercubicUnshift_shift] using hsource'
  have hfirst : periodicHypercubicPlaquetteFirstAxis p = (0 : PeriodicHypercubicAxis) :=
    (periodicHypercubicEvenPlaquetteHasTimeDirection_iff_firstAxis_zero p).1
      ((periodicHypercubicEven_mem_positiveBoundaryTemporalPlaquettes p).1
        (Finset.mem_sdiff.mp hpResidual).1).1
  have hpEq :
      p = periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H j := by
    apply Prod.ext hbase.symm
    apply Subtype.ext
    exact Prod.ext hfirst hdirection.symm
  have hpNotSelected := (Finset.mem_sdiff.mp hpResidual).2
  apply hpNotSelected
  rw [hpEq]
  exact periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion_mem_set H j

private theorem
    periodicHypercubicEvenAntipodalStepThree_not_primaryCompanionUpperSpatialRange
    {H : ℕ}
    (hH : 1 < H)
    (p : PeriodicHypercubicEvenPlaquette H)
    (hantipodal : periodicHypercubicEvenPositiveBoundaryTemporalAntipodalEdgePattern H p) :
    ¬ ∃ j : Fin 4,
      periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionUpperSpatialEdgeEmbedding
          H (Nat.zero_lt_of_lt hH) j =
        (⟨(periodicHypercubicBoundaryStep
            (PeriodicHypercubicEvenSideLength H) p 3).edge,
          hantipodal.2.2.2.2⟩ :
          (periodicHypercubicEvenEdgeOrbitPartition H).PositiveEdge) := by
  rintro ⟨j, hj⟩
  have hval := congrArg Subtype.val hj
  change
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionUpperSpatialEdge H j =
      (periodicHypercubicBoundaryStep
        (PeriodicHypercubicEvenSideLength H) p 3).edge at hval
  have hsource := congrArg Prod.fst hval
  rw [periodicHypercubicBoundaryStep_three] at hsource
  have htime := congrArg (fun v => (v 0).val) hsource
  change
    ((periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionUpperSpatialEdge H j).1 0).val =
      (p.1 0).val at htime
  rw [periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionUpperSpatialEdge_source_time_val_one,
    hantipodal.1] at htime
  omega

/-- On the canonical four-companion open-half section, every *residual*
positive-boundary temporal open path is exactly the identity once `H > 1`.

The two temporal incidences are always identity because the section only
changes four spatial edges.  On the primary side, equality of a residual
spatial incidence with one of those four edges would force the plaquette itself
to be one of the selected companions.  On the antipodal side, the residual
spatial incidence is based at time `H`, whereas all four selected edges are
based at time `1`. -/
theorem
    periodicHypercubicEvenPositiveBoundaryTemporalResidualFiberedOpenPath_fourCompanionSection_eq_one
    (H N : ℕ)
    (hH : 1 < H)
    (u : Fin 4 → Matrix.specialUnitaryGroup (Fin N) ℂ)
    (p : PeriodicHypercubicEvenPlaquette H)
    (hpResidual :
      p ∈ periodicHypercubicEvenPositiveBoundaryTemporalResidualPlaquettes H) :
    periodicHypercubicEvenPositiveBoundaryTemporalFiberedOpenPath
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfSection
          H (Nat.zero_lt_of_lt hH) u) p = 1 := by
  let P := periodicHypercubicEvenEdgeOrbitPartition H
  let Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ
  let hH0 : 0 < H := Nat.zero_lt_of_lt hH
  let x :=
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfSection
      H hH0 u
  let A := P.boundaryFiberedAssemble
    (fun _ => (1 : Gauge)) x (fun _ => (1 : Gauge))
  have hpPositive : periodicHypercubicEvenPositiveBoundaryTemporalPlaquette p :=
    (periodicHypercubicEven_mem_positiveBoundaryTemporalPlaquettes p).1
      (Finset.mem_sdiff.mp hpResidual).1
  have hmu : periodicHypercubicPlaquetteFirstAxis p = (0 : PeriodicHypercubicAxis) :=
    (periodicHypercubicEvenPlaquetteHasTimeDirection_iff_firstAxis_zero p).1 hpPositive.1
  have hpattern :=
    periodicHypercubicEvenPositiveBoundaryTemporalPlaquette_exact_edge_pattern
      hH0 p hpPositive
  have hstep_of_edge_one (k : Fin 4)
      (hk : P.side
          (periodicHypercubicBoundaryStep
            (PeriodicHypercubicEvenSideLength H) p k).edge =
        ReflectionEdgeSide.positive)
      (hx : x
          (⟨(periodicHypercubicBoundaryStep
              (PeriodicHypercubicEvenSideLength H) p k).edge, hk⟩ : P.PositiveEdge) = 1) :
      periodicHypercubicStepValue A
          (periodicHypercubicBoundaryStep
            (PeriodicHypercubicEvenSideLength H) p k) = 1 := by
    have hA :
        A (periodicHypercubicBoundaryStep
            (PeriodicHypercubicEvenSideLength H) p k).edge = 1 := by
      calc
        A (periodicHypercubicBoundaryStep
            (PeriodicHypercubicEvenSideLength H) p k).edge =
          x (⟨(periodicHypercubicBoundaryStep
                (PeriodicHypercubicEvenSideLength H) p k).edge, hk⟩ : P.PositiveEdge) := by
            exact P.boundaryFiberedAssemble_positive
              (fun _ => (1 : Gauge)) x (fun _ => (1 : Gauge))
              ⟨(periodicHypercubicBoundaryStep
                (PeriodicHypercubicEvenSideLength H) p k).edge, hk⟩
        _ = 1 := hx
    cases horientation :
      (periodicHypercubicBoundaryStep
        (PeriodicHypercubicEvenSideLength H) p k).orientation <;>
      simp [periodicHypercubicStepValue, horientation, hA]
  rcases hpattern with hprimary | hantipodal
  · unfold periodicHypercubicEvenPositiveBoundaryTemporalPrimaryEdgePattern at hprimary
    have hx0 : x
        (⟨(periodicHypercubicBoundaryStep
            (PeriodicHypercubicEvenSideLength H) p 0).edge,
          hprimary.2.1⟩ : P.PositiveEdge) = 1 := by
      apply periodicHypercubicEvenPrimaryCompanionOpenHalfSection_eq_one_of_direction_zero
      simpa [periodicHypercubicBoundaryStep_zero, hmu]
    have hx1 : x
        (⟨(periodicHypercubicBoundaryStep
            (PeriodicHypercubicEvenSideLength H) p 1).edge,
          hprimary.2.2.1⟩ : P.PositiveEdge) = 1 := by
      unfold x
      unfold periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfSection
      rw [dif_neg]
      exact periodicHypercubicEvenPrimaryResidualStepOne_not_primaryCompanionUpperSpatialRange
        hH0 p hpResidual hprimary
    have hx2 : x
        (⟨(periodicHypercubicBoundaryStep
            (PeriodicHypercubicEvenSideLength H) p 2).edge,
          hprimary.2.2.2.1⟩ : P.PositiveEdge) = 1 := by
      apply periodicHypercubicEvenPrimaryCompanionOpenHalfSection_eq_one_of_direction_zero
      simpa [periodicHypercubicBoundaryStep_two, hmu]
    have hs0 := hstep_of_edge_one 0 hprimary.2.1 hx0
    have hs1 := hstep_of_edge_one 1 hprimary.2.2.1 hx1
    have hs2 := hstep_of_edge_one 2 hprimary.2.2.2.1 hx2
    change periodicHypercubicEvenPositiveBoundaryTemporalOpenPath A p = 1
    unfold periodicHypercubicEvenPositiveBoundaryTemporalOpenPath
    rw [if_pos hprimary.1, hs0, hs1, hs2]
    simp
  · unfold periodicHypercubicEvenPositiveBoundaryTemporalAntipodalEdgePattern at hantipodal
    have hbaseNe : (p.1 0).val ≠ 0 := by omega
    have hx0 : x
        (⟨(periodicHypercubicBoundaryStep
            (PeriodicHypercubicEvenSideLength H) p 0).edge,
          hantipodal.2.1⟩ : P.PositiveEdge) = 1 := by
      apply periodicHypercubicEvenPrimaryCompanionOpenHalfSection_eq_one_of_direction_zero
      simpa [periodicHypercubicBoundaryStep_zero, hmu]
    have hx2 : x
        (⟨(periodicHypercubicBoundaryStep
            (PeriodicHypercubicEvenSideLength H) p 2).edge,
          hantipodal.2.2.2.1⟩ : P.PositiveEdge) = 1 := by
      apply periodicHypercubicEvenPrimaryCompanionOpenHalfSection_eq_one_of_direction_zero
      simpa [periodicHypercubicBoundaryStep_two, hmu]
    have hx3 : x
        (⟨(periodicHypercubicBoundaryStep
            (PeriodicHypercubicEvenSideLength H) p 3).edge,
          hantipodal.2.2.2.2⟩ : P.PositiveEdge) = 1 := by
      unfold x
      unfold periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfSection
      rw [dif_neg]
      exact periodicHypercubicEvenAntipodalStepThree_not_primaryCompanionUpperSpatialRange
        hH p hantipodal
    have hs0 := hstep_of_edge_one 0 hantipodal.2.1 hx0
    have hs2 := hstep_of_edge_one 2 hantipodal.2.2.2.1 hx2
    have hs3 := hstep_of_edge_one 3 hantipodal.2.2.2.2 hx3
    change periodicHypercubicEvenPositiveBoundaryTemporalOpenPath A p = 1
    unfold periodicHypercubicEvenPositiveBoundaryTemporalOpenPath
    rw [if_neg hbaseNe, hs2, hs3, hs0]
    simp

end

end MathlibAnalytic
end MGAP4D
