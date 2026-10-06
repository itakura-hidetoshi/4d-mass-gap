import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentOrbitGeometryFiniteRepresentation
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimarySpatialEdgeTemporalCompanion
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPlaquetteLocalBaseL1Separation
import Mathlib.Tactic

/-!
# Primary-plaquette seed distance for the adjacent SU(2) posterior locality route

The actual three-mode adjacent Krylov orbit starts from one of the first three
Gram--Schmidt modes of the canonical primary spatial plaquette.  This file puts
the four physical links of that plaquette on the same spatial-slice link carrier
used by the posterior response theorems, and defines the exact periodic
link-base L1 distance to that four-link seed.

The radius-two exterior is strong enough to discharge, for every seed link,
the two geometric hypotheses used by the existing posterior covariance theorem:
the links are distinct and they are not Wilson-plaquette-local.

This is only the P3-A geometric interface.  It does not assert that a positive
transfer power has finite hard support, and it does not estimate the retained
output / half-density drift.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance p3PrimarySeedSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance p3PrimarySeedSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) :=
  ⟨by simp [PeriodicHypercubicEvenSideLength]⟩

/-- The k-th physical edge of the canonical primary spatial plaquette, viewed
on the canonical time-zero spatial-slice link carrier. -/
noncomputable def physicalYangMillsSU2PrimaryPlaquetteSeedLink
    (H : ℕ) (k : Fin 4) :
    PeriodicHypercubicEvenSpatialSliceLink H :=
  (⟨(periodicHypercubicEvenPrimarySpatialPlaquetteEdge H k).1, by
      unfold periodicHypercubicEvenOnPrimaryReflectionPlane
      apply ZMod.val_injective
      simpa using
        periodicHypercubicEvenPrimarySpatialPlaquetteEdge_source_time_val_zero H k⟩,
    ⟨(periodicHypercubicEvenPrimarySpatialPlaquetteEdge H k).2,
      periodicHypercubicEvenPrimarySpatialPlaquetteEdge_direction_ne_zero H k⟩)

/-- Returning the seed link to the four-dimensional positive-edge carrier
recovers exactly the original primary-plaquette edge. -/
@[simp] theorem physicalYangMillsSU2PrimaryPlaquetteSeedLink_embedding
    (H : ℕ) (k : Fin 4) :
    periodicHypercubicEvenSpatialSliceLinkEmbedding H
        (physicalYangMillsSU2PrimaryPlaquetteSeedLink H k) =
      periodicHypercubicEvenPrimarySpatialPlaquetteEdge H k := by
  rfl

/-- Periodic link-base L1 distance from an arbitrary spatial source link to the
nearest of the four canonical primary-plaquette seed links.  The explicit
fourfold minimum keeps the distance interface proof-transparent. -/
def physicalYangMillsSU2PrimaryPlaquetteSeedDistance
    (H : ℕ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) : ℕ :=
  min
    (periodicHypercubicEdgeBaseL1Distance
      (PeriodicHypercubicEvenSideLength H)
      (periodicHypercubicEvenSpatialSliceLinkEmbedding H
        (physicalYangMillsSU2PrimaryPlaquetteSeedLink H 0))
      (periodicHypercubicEvenSpatialSliceLinkEmbedding H source))
    (min
      (periodicHypercubicEdgeBaseL1Distance
        (PeriodicHypercubicEvenSideLength H)
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H
          (physicalYangMillsSU2PrimaryPlaquetteSeedLink H 1))
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H source))
      (min
        (periodicHypercubicEdgeBaseL1Distance
          (PeriodicHypercubicEvenSideLength H)
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H
            (physicalYangMillsSU2PrimaryPlaquetteSeedLink H 2))
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H source))
        (periodicHypercubicEdgeBaseL1Distance
          (PeriodicHypercubicEvenSideLength H)
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H
            (physicalYangMillsSU2PrimaryPlaquetteSeedLink H 3))
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H source))))

/-- The seed distance is below the distance to every one of the four seed
links. -/
theorem physicalYangMillsSU2PrimaryPlaquetteSeedDistance_le_seed
    (H : ℕ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k : Fin 4) :
    physicalYangMillsSU2PrimaryPlaquetteSeedDistance H source ≤
      periodicHypercubicEdgeBaseL1Distance
        (PeriodicHypercubicEvenSideLength H)
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H
          (physicalYangMillsSU2PrimaryPlaquetteSeedLink H k))
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H source) := by
  let d : Fin 4 → ℕ := fun j =>
    periodicHypercubicEdgeBaseL1Distance
      (PeriodicHypercubicEvenSideLength H)
      (periodicHypercubicEvenSpatialSliceLinkEmbedding H
        (physicalYangMillsSU2PrimaryPlaquetteSeedLink H j))
      (periodicHypercubicEvenSpatialSliceLinkEmbedding H source)
  change min (d 0) (min (d 1) (min (d 2) (d 3))) ≤ d k
  fin_cases k
  · exact min_le_left _ _
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))
  · exact (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))

/-- Every literal seed link has seed distance zero. -/
@[simp] theorem physicalYangMillsSU2PrimaryPlaquetteSeedDistance_seed
    (H : ℕ) (k : Fin 4) :
    physicalYangMillsSU2PrimaryPlaquetteSeedDistance H
      (physicalYangMillsSU2PrimaryPlaquetteSeedLink H k) = 0 := by
  have hle :=
    physicalYangMillsSU2PrimaryPlaquetteSeedDistance_le_seed H
      (physicalYangMillsSU2PrimaryPlaquetteSeedLink H k) k
  have hle0 :
      physicalYangMillsSU2PrimaryPlaquetteSeedDistance H
        (physicalYangMillsSU2PrimaryPlaquetteSeedLink H k) ≤ 0 := by
    simpa using hle
  omega

/-- Radius-R links around the actual four-link primary-plaquette seed. -/
noncomputable def physicalYangMillsSU2PrimaryPlaquetteNearLinks
    (H radius : ℕ) :
    Finset (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Finset.univ.filter
    (fun source =>
      physicalYangMillsSU2PrimaryPlaquetteSeedDistance H source ≤ radius)

/-- Complementary exterior links, expressed directly by strict seed distance. -/
noncomputable def physicalYangMillsSU2PrimaryPlaquetteFarLinks
    (H radius : ℕ) :
    Finset (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Finset.univ.filter
    (fun source =>
      radius < physicalYangMillsSU2PrimaryPlaquetteSeedDistance H source)

@[simp] theorem physicalYangMillsSU2PrimaryPlaquette_mem_nearLinks
    (H radius : ℕ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    source ∈ physicalYangMillsSU2PrimaryPlaquetteNearLinks H radius ↔
      physicalYangMillsSU2PrimaryPlaquetteSeedDistance H source ≤ radius := by
  simp [physicalYangMillsSU2PrimaryPlaquetteNearLinks]

@[simp] theorem physicalYangMillsSU2PrimaryPlaquette_mem_farLinks
    (H radius : ℕ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    source ∈ physicalYangMillsSU2PrimaryPlaquetteFarLinks H radius ↔
      radius < physicalYangMillsSU2PrimaryPlaquetteSeedDistance H source := by
  simp [physicalYangMillsSU2PrimaryPlaquetteFarLinks]

/-- Near and far links are an exact finite partition of the spatial-link
carrier at every radius. -/
theorem physicalYangMillsSU2PrimaryPlaquette_near_union_far
    (H radius : ℕ) :
    physicalYangMillsSU2PrimaryPlaquetteNearLinks H radius ∪
        physicalYangMillsSU2PrimaryPlaquetteFarLinks H radius =
      Finset.univ := by
  ext source
  simp
  omega

theorem physicalYangMillsSU2PrimaryPlaquette_near_disjoint_far
    (H radius : ℕ) :
    Disjoint
      (physicalYangMillsSU2PrimaryPlaquetteNearLinks H radius)
      (physicalYangMillsSU2PrimaryPlaquetteFarLinks H radius) := by
  refine Finset.disjoint_left.mpr ?_
  intro source hNear hFar
  have hn :=
    (physicalYangMillsSU2PrimaryPlaquette_mem_nearLinks H radius source).mp hNear
  have hf :=
    (physicalYangMillsSU2PrimaryPlaquette_mem_farLinks H radius source).mp hFar
  omega

/-- Seed distance strictly greater than two simultaneously gives the exact
distinctness and non-plaquette-local hypotheses required by the existing
posterior covariance decay theorem, for every one of the four seed links. -/
theorem physicalYangMillsSU2PrimaryPlaquetteSeedDistance_gt_two_remote
    (H : ℕ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hFar : 2 < physicalYangMillsSU2PrimaryPlaquetteSeedDistance H source)
    (k : Fin 4) :
    physicalYangMillsSU2PrimaryPlaquetteSeedLink H k ≠ source ∧
      ¬ periodicHypercubicEvenPlaquetteLocal H
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H
          (physicalYangMillsSU2PrimaryPlaquetteSeedLink H k))
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H source) := by
  have hSeedLe :=
    physicalYangMillsSU2PrimaryPlaquetteSeedDistance_le_seed H source k
  constructor
  · intro hEq
    subst source
    have hZero :=
      physicalYangMillsSU2PrimaryPlaquetteSeedDistance_seed H k
    omega
  · intro hLocal
    have hTwo :=
      periodicHypercubicEvenPlaquetteLocal_edgeBaseL1Distance_le_two
        H
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H
          (physicalYangMillsSU2PrimaryPlaquetteSeedLink H k))
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H source)
        hLocal
    omega

/-- Membership in the radius-two exterior is the finite-set form of the same
remote geometry package. -/
theorem physicalYangMillsSU2PrimaryPlaquetteFarLinks_two_remote
    (H : ℕ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hFar : source ∈ physicalYangMillsSU2PrimaryPlaquetteFarLinks H 2)
    (k : Fin 4) :
    physicalYangMillsSU2PrimaryPlaquetteSeedLink H k ≠ source ∧
      ¬ periodicHypercubicEvenPlaquetteLocal H
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H
          (physicalYangMillsSU2PrimaryPlaquetteSeedLink H k))
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H source) := by
  exact physicalYangMillsSU2PrimaryPlaquetteSeedDistance_gt_two_remote
    H source
    ((physicalYangMillsSU2PrimaryPlaquette_mem_farLinks H 2 source).mp hFar)
    k

/-- At Krylov depth zero the actual fine pair orbit is literally one of the
three canonical primary-plaquette Gram--Schmidt seed modes. -/
@[simp] theorem physicalYangMillsSU2AdjacentFinePairOrbitVector_zero
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    (n : ℕ) (k : Fin 3) :
    physicalYangMillsSU2AdjacentFinePairOrbitVector
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n 0 k =
      periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeMode
        (halfExtent (n + 1)) k := by
  simp [physicalYangMillsSU2AdjacentFinePairOrbitVector]

/-- Consequently the r=0 member of the actual frozen family is exactly one
coarse-coupling transfer applied to that primary-plaquette seed mode. -/
theorem physicalYangMillsSU2AdjacentFinePairFrozenCouplingStepVector_zero
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    (n : ℕ) (k : Fin 3) :
    physicalYangMillsSU2AdjacentFinePairFrozenCouplingStepVector
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n 0 k =
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
        (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
        (beta n) (hbeta n)
        (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeMode
          (halfExtent (n + 1)) k) := by
  simp [physicalYangMillsSU2AdjacentFinePairFrozenCouplingStepVector,
    physicalYangMillsSU2AdjacentFinePairOrbitVector]

end

end MathlibAnalytic
end MGAP4D
