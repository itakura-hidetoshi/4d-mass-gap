import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimarySpatialCyclicFourLegFockPullback
import MGAP4D.MathlibAnalytic.PeriodicHypercubicPlaquetteIncidence

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The canonical primary temporal companion always has the primary fixed-plane
incidence pattern.  This packages the geometric fact that its three open-path
incidences are steps `0,1,2`, while step `3` is the selected fixed boundary
edge. -/
theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion_primaryEdgePattern
    (H : ℕ) (hH : 0 < H) (k : Fin 4) :
    periodicHypercubicEvenPositiveBoundaryTemporalPrimaryEdgePattern H
      (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k) := by
  have hpattern :=
    periodicHypercubicEvenPositiveBoundaryTemporalPlaquette_exact_edge_pattern
      hH
      (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k)
      (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion_positiveBoundary H k)
  rcases hpattern with hprimary | hantipodal
  · exact hprimary
  · have hzero :=
      periodicHypercubicEvenPrimarySpatialPlaquetteEdge_source_time_val_zero H k
    have hHbase := hantipodal.1
    change
      ((periodicHypercubicEvenPrimarySpatialPlaquetteEdge H k).1 0).val = H at hHbase
    omega

/-- The physical spatial edge in step `1` of the `k`-th primary temporal
companion.  It is the original fixed spatial edge translated one lattice unit
into the positive time half. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionUpperSpatialEdge
    (H : ℕ) (k : Fin 4) : PeriodicHypercubicEvenEdge H :=
  (periodicHypercubicBoundaryStep
    (PeriodicHypercubicEvenSideLength H)
    (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k) 1).edge

@[simp] theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionUpperSpatialEdge_eq
    (H : ℕ) (k : Fin 4) :
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionUpperSpatialEdge H k =
      (periodicHypercubicShift
          (PeriodicHypercubicEvenSideLength H)
          (periodicHypercubicEvenPrimarySpatialPlaquetteEdge H k).1
          (0 : PeriodicHypercubicAxis),
        (periodicHypercubicEvenPrimarySpatialPlaquetteEdge H k).2) := by
  rfl

/-- The four upper spatial edges are pairwise distinct.  Time translation is
cancelled by the existing `shift/unshift` inverse, reducing injectivity exactly
to injectivity of the four physical boundary edges. -/
theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionUpperSpatialEdge_injective
    (H : ℕ) :
    Function.Injective
      (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionUpperSpatialEdge H) := by
  intro i j hij
  rw [periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionUpperSpatialEdge_eq,
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionUpperSpatialEdge_eq] at hij
  have hsource :
      periodicHypercubicShift
          (PeriodicHypercubicEvenSideLength H)
          (periodicHypercubicEvenPrimarySpatialPlaquetteEdge H i).1
          (0 : PeriodicHypercubicAxis) =
        periodicHypercubicShift
          (PeriodicHypercubicEvenSideLength H)
          (periodicHypercubicEvenPrimarySpatialPlaquetteEdge H j).1
          (0 : PeriodicHypercubicAxis) :=
    congrArg Prod.fst hij
  have hdirection :
      (periodicHypercubicEvenPrimarySpatialPlaquetteEdge H i).2 =
        (periodicHypercubicEvenPrimarySpatialPlaquetteEdge H j).2 :=
    congrArg Prod.snd hij
  have hsource' := congrArg
    (fun v => periodicHypercubicUnshift
      (PeriodicHypercubicEvenSideLength H) v (0 : PeriodicHypercubicAxis))
    hsource
  simp only [periodicHypercubicUnshift_shift] at hsource'
  apply periodicHypercubicEvenPrimarySpatialPlaquetteEdge_injective H
  exact Prod.ext hsource' hdirection

/-- The translated upper spatial edge belongs to the positive open-half edge
carrier. -/
theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionUpperSpatialEdge_side_positive
    (H : ℕ) (hH : 0 < H) (k : Fin 4) :
    (periodicHypercubicEvenEdgeOrbitPartition H).side
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionUpperSpatialEdge H k) =
      ReflectionEdgeSide.positive := by
  exact
    (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion_primaryEdgePattern
      H hH k).2.2.1

/-- Embedding of the four independently selected upper spatial edges into the
actual positive open-half edge index. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionUpperSpatialEdgeEmbedding
    (H : ℕ) (hH : 0 < H) :
    Fin 4 ↪ (periodicHypercubicEvenEdgeOrbitPartition H).PositiveEdge where
  toFun k :=
    ⟨periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionUpperSpatialEdge H k,
      periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionUpperSpatialEdge_side_positive
        H hH k⟩
  inj' := by
    intro i j hij
    apply
      periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionUpperSpatialEdge_injective H
    exact Subtype.ext_iff.mp hij

/-- Step `0` of the primary companion as an actual positive open-half edge. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionStepZeroPositiveEdge
    (H : ℕ) (hH : 0 < H) (k : Fin 4) :
    (periodicHypercubicEvenEdgeOrbitPartition H).PositiveEdge :=
  ⟨(periodicHypercubicBoundaryStep
      (PeriodicHypercubicEvenSideLength H)
      (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k) 0).edge,
    (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion_primaryEdgePattern
      H hH k).2.1⟩

/-- Step `2` of the primary companion as an actual positive open-half edge. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionStepTwoPositiveEdge
    (H : ℕ) (hH : 0 < H) (k : Fin 4) :
    (periodicHypercubicEvenEdgeOrbitPartition H).PositiveEdge :=
  ⟨(periodicHypercubicBoundaryStep
      (PeriodicHypercubicEvenSideLength H)
      (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k) 2).edge,
    (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion_primaryEdgePattern
      H hH k).2.2.2.1⟩

/-- No temporal step `0` can coincide with one of the selected upper spatial
edges, because the former has direction `0` while every primary plaquette edge
is spatial. -/
theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionStepZero_not_upperSpatialRange
    (H : ℕ) (hH : 0 < H) (k : Fin 4) :
    ¬ ∃ j : Fin 4,
      periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionUpperSpatialEdgeEmbedding
          H hH j =
        periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionStepZeroPositiveEdge
          H hH k := by
  rintro ⟨j, hj⟩
  have hval := congrArg Subtype.val hj
  have hdir := congrArg Prod.snd hval
  apply periodicHypercubicEvenPrimarySpatialPlaquetteEdge_direction_ne_zero H j
  simpa [
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionUpperSpatialEdge,
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionStepZeroPositiveEdge,
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion,
    periodicHypercubicEvenPrimarySpatialEdgeTemporalCompanion] using hdir

/-- No temporal step `2` can coincide with one of the selected upper spatial
edges. -/
theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionStepTwo_not_upperSpatialRange
    (H : ℕ) (hH : 0 < H) (k : Fin 4) :
    ¬ ∃ j : Fin 4,
      periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionUpperSpatialEdgeEmbedding
          H hH j =
        periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionStepTwoPositiveEdge
          H hH k := by
  rintro ⟨j, hj⟩
  have hval := congrArg Subtype.val hj
  have hdir := congrArg Prod.snd hval
  apply periodicHypercubicEvenPrimarySpatialPlaquetteEdge_direction_ne_zero H j
  simpa [
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionUpperSpatialEdge,
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionStepTwoPositiveEdge,
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion,
    periodicHypercubicEvenPrimarySpatialEdgeTemporalCompanion] using hdir

/-- Actual positive-open-half configuration realizing an arbitrary four-tuple
of group values on the four upper spatial companion edges and setting every
other positive edge to the identity. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfSection
    (H : ℕ) (hH : 0 < H)
    {Gauge : Type} [Group Gauge]
    (u : Fin 4 → Gauge) :
    (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration Gauge :=
  fun e =>
    if _h : ∃ k : Fin 4,
        periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionUpperSpatialEdgeEmbedding
          H hH k = e then
      u (Function.invFun
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionUpperSpatialEdgeEmbedding
          H hH) e)
    else
      1

@[simp] theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfSection_upperSpatial
    (H : ℕ) (hH : 0 < H)
    {Gauge : Type} [Group Gauge]
    (u : Fin 4 → Gauge) (k : Fin 4) :
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfSection
        H hH u
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionUpperSpatialEdgeEmbedding
          H hH k) =
      u k := by
  unfold periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfSection
  rw [dif_pos ⟨k, rfl⟩]
  have hinv := Function.leftInverse_invFun
    (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionUpperSpatialEdgeEmbedding
      H hH).injective k
  rw [hinv]

@[simp] theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfSection_stepZero
    (H : ℕ) (hH : 0 < H)
    {Gauge : Type} [Group Gauge]
    (u : Fin 4 → Gauge) (k : Fin 4) :
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfSection
        H hH u
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionStepZeroPositiveEdge
          H hH k) =
      1 := by
  unfold periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfSection
  rw [dif_neg
    (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionStepZero_not_upperSpatialRange
      H hH k)]

@[simp] theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfSection_stepTwo
    (H : ℕ) (hH : 0 < H)
    {Gauge : Type} [Group Gauge]
    (u : Fin 4 → Gauge) (k : Fin 4) :
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfSection
        H hH u
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionStepTwoPositiveEdge
          H hH k) =
      1 := by
  unfold periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfSection
  rw [dif_neg
    (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionStepTwo_not_upperSpatialRange
      H hH k)]

/-- The actual fibered open path of each primary temporal companion recovers the
prescribed four-tuple exactly.  The two temporal incidences are identity and
the middle upper spatial incidence carries the selected value. -/
theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenPath_section
    (H : ℕ) (hH : 0 < H)
    {Gauge : Type} [Group Gauge]
    (u : Fin 4 → Gauge) (k : Fin 4) :
    periodicHypercubicEvenPositiveBoundaryTemporalFiberedOpenPath
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfSection
          H hH u)
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k) =
      u k := by
  let P := periodicHypercubicEvenEdgeOrbitPartition H
  let p := periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k
  let x :=
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfSection
      H hH u
  let A := P.boundaryFiberedAssemble
    (fun _ => (1 : Gauge)) x (fun _ => (1 : Gauge))
  have hbase : (p.1 0).val = 0 := by
    change ((periodicHypercubicEvenPrimarySpatialPlaquetteEdge H k).1 0).val = 0
    exact periodicHypercubicEvenPrimarySpatialPlaquetteEdge_source_time_val_zero H k
  have hA0 :
      A (periodicHypercubicBoundaryStep
          (PeriodicHypercubicEvenSideLength H) p 0).edge = 1 := by
    calc
      A (periodicHypercubicBoundaryStep
          (PeriodicHypercubicEvenSideLength H) p 0).edge =
        x (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionStepZeroPositiveEdge
          H hH k) := by
            exact P.boundaryFiberedAssemble_positive
              (fun _ => (1 : Gauge)) x (fun _ => (1 : Gauge))
              (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionStepZeroPositiveEdge
                H hH k)
      _ = 1 := by
        exact
          periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfSection_stepZero
            H hH u k
  have hA1 :
      A (periodicHypercubicBoundaryStep
          (PeriodicHypercubicEvenSideLength H) p 1).edge = u k := by
    calc
      A (periodicHypercubicBoundaryStep
          (PeriodicHypercubicEvenSideLength H) p 1).edge =
        x (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionUpperSpatialEdgeEmbedding
          H hH k) := by
            exact P.boundaryFiberedAssemble_positive
              (fun _ => (1 : Gauge)) x (fun _ => (1 : Gauge))
              (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionUpperSpatialEdgeEmbedding
                H hH k)
      _ = u k := by
        exact
          periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfSection_upperSpatial
            H hH u k
  have hA2 :
      A (periodicHypercubicBoundaryStep
          (PeriodicHypercubicEvenSideLength H) p 2).edge = 1 := by
    calc
      A (periodicHypercubicBoundaryStep
          (PeriodicHypercubicEvenSideLength H) p 2).edge =
        x (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionStepTwoPositiveEdge
          H hH k) := by
            exact P.boundaryFiberedAssemble_positive
              (fun _ => (1 : Gauge)) x (fun _ => (1 : Gauge))
              (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionStepTwoPositiveEdge
                H hH k)
      _ = 1 := by
        exact
          periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfSection_stepTwo
            H hH u k
  have hs0 :
      periodicHypercubicStepValue A
          (periodicHypercubicBoundaryStep
            (PeriodicHypercubicEvenSideLength H) p 0) = 1 := by
    change A (periodicHypercubicBoundaryStep
      (PeriodicHypercubicEvenSideLength H) p 0).edge = 1
    exact hA0
  have hs1 :
      periodicHypercubicStepValue A
          (periodicHypercubicBoundaryStep
            (PeriodicHypercubicEvenSideLength H) p 1) = u k := by
    change A (periodicHypercubicBoundaryStep
      (PeriodicHypercubicEvenSideLength H) p 1).edge = u k
    exact hA1
  have hs2 :
      periodicHypercubicStepValue A
          (periodicHypercubicBoundaryStep
            (PeriodicHypercubicEvenSideLength H) p 2) = 1 := by
    change (A (periodicHypercubicBoundaryStep
      (PeriodicHypercubicEvenSideLength H) p 2).edge)⁻¹ = 1
    rw [hA2]
    simp
  change periodicHypercubicEvenPositiveBoundaryTemporalOpenPath A p = u k
  rw [show (p.1 0).val = 0 from hbase]
  simp only [periodicHypercubicEvenPositiveBoundaryTemporalOpenPath, if_pos]
  rw [hs0, hs1, hs2]
  simp

/-- The four primary temporal-companion open paths as one actual open-half map. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenPathTuple
    (H N : ℕ)
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    Fin 4 → Matrix.specialUnitaryGroup (Fin N) ℂ :=
  fun k =>
    periodicHypercubicEvenPositiveBoundaryTemporalFiberedOpenPath x
      (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k)

/-- The section is a literal right inverse of the actual four-companion open
path map. -/
theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenPathTuple_section
    (H N : ℕ) (hH : 0 < H)
    (u : Fin 4 → Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenPathTuple
        H N
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfSection
          H hH u) =
      u := by
  funext k
  exact
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenPath_section
      H hH u k

/-- Every abstract four-edge `SU(N)` tuple is realized by an actual positive
open-half lattice configuration through the four primary temporal companions. -/
theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenPathTuple_surjective
    (H N : ℕ) (hH : 0 < H) :
    Function.Surjective
      (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenPathTuple H N) := by
  intro u
  exact ⟨
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfSection H hH u,
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenPathTuple_section
      H N hH u⟩

/-- On the actual section, the open-half cyclic holonomy is exactly the abstract
four-edge cyclic plaquette word. -/
theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfCyclicHolonomy_section
    (H N : ℕ) (hH : 0 < H)
    (u : Fin 4 → Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfCyclicHolonomy
        H N
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfSection
          H hH u) =
      haarFinFourCyclicPlaquetteWord u := by
  unfold periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfCyclicHolonomy
  congr 1
  funext k
  exact
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenPath_section
      H hH u k

end

end MathlibAnalytic
end MGAP4D
