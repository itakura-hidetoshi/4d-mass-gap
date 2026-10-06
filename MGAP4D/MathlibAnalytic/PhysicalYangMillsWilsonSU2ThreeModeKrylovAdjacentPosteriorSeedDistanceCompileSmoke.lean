import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPosteriorSeedDistance

/-! Compile contracts for the P3-A primary-plaquette seed-distance interface. -/

namespace MGAP4D.MathlibAnalytic

noncomputable section

#check physicalYangMillsSU2PrimaryPlaquetteSeedLink
#check physicalYangMillsSU2PrimaryPlaquetteSeedLink_embedding
#check physicalYangMillsSU2PrimaryPlaquetteSeedDistance
#check physicalYangMillsSU2PrimaryPlaquetteSeedDistance_le_seed
#check physicalYangMillsSU2PrimaryPlaquetteSeedDistance_seed
#check physicalYangMillsSU2PrimaryPlaquetteNearLinks
#check physicalYangMillsSU2PrimaryPlaquetteFarLinks
#check physicalYangMillsSU2PrimaryPlaquette_near_union_far
#check physicalYangMillsSU2PrimaryPlaquette_near_disjoint_far
#check physicalYangMillsSU2PrimaryPlaquetteSeedDistance_gt_two_remote
#check physicalYangMillsSU2PrimaryPlaquetteFarLinks_two_remote
#check physicalYangMillsSU2AdjacentFinePairOrbitVector_zero
#check physicalYangMillsSU2AdjacentFinePairFrozenCouplingStepVector_zero

section Geometry

variable (H radius : ℕ)
variable (source : PeriodicHypercubicEvenSpatialSliceLink H)

example (k : Fin 4) :
    periodicHypercubicEvenSpatialSliceLinkEmbedding H
        (physicalYangMillsSU2PrimaryPlaquetteSeedLink H k) =
      periodicHypercubicEvenPrimarySpatialPlaquetteEdge H k :=
  physicalYangMillsSU2PrimaryPlaquetteSeedLink_embedding H k

example (k : Fin 4) :
    physicalYangMillsSU2PrimaryPlaquetteSeedDistance H source ≤
      periodicHypercubicEdgeBaseL1Distance
        (PeriodicHypercubicEvenSideLength H)
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H
          (physicalYangMillsSU2PrimaryPlaquetteSeedLink H k))
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H source) :=
  physicalYangMillsSU2PrimaryPlaquetteSeedDistance_le_seed H source k

example (k : Fin 4) :
    physicalYangMillsSU2PrimaryPlaquetteSeedDistance H
      (physicalYangMillsSU2PrimaryPlaquetteSeedLink H k) = 0 :=
  physicalYangMillsSU2PrimaryPlaquetteSeedDistance_seed H k

example
    (hFar : source ∈ physicalYangMillsSU2PrimaryPlaquetteFarLinks H 2)
    (k : Fin 4) :
    physicalYangMillsSU2PrimaryPlaquetteSeedLink H k ≠ source ∧
      ¬ periodicHypercubicEvenPlaquetteLocal H
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H
          (physicalYangMillsSU2PrimaryPlaquetteSeedLink H k))
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H source) :=
  physicalYangMillsSU2PrimaryPlaquetteFarLinks_two_remote H source hFar k

end Geometry

section Frozen

variable {halfExtent : ℕ → ℕ}
variable {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n : ℕ) (k : Fin 3)

example :
    physicalYangMillsSU2AdjacentFinePairOrbitVector
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n 0 k =
      periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeMode
        (halfExtent (n + 1)) k :=
  physicalYangMillsSU2AdjacentFinePairOrbitVector_zero n k

example :
    physicalYangMillsSU2AdjacentFinePairFrozenCouplingStepVector
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n 0 k =
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
        (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
        (beta n) (hbeta n)
        (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeMode
          (halfExtent (n + 1)) k) :=
  physicalYangMillsSU2AdjacentFinePairFrozenCouplingStepVector_zero n k

end Frozen

#print axioms physicalYangMillsSU2PrimaryPlaquetteSeedDistance_le_seed
#print axioms physicalYangMillsSU2PrimaryPlaquetteSeedDistance_seed
#print axioms physicalYangMillsSU2PrimaryPlaquette_near_union_far
#print axioms physicalYangMillsSU2PrimaryPlaquette_near_disjoint_far
#print axioms physicalYangMillsSU2PrimaryPlaquetteSeedDistance_gt_two_remote
#print axioms physicalYangMillsSU2PrimaryPlaquetteFarLinks_two_remote
#print axioms physicalYangMillsSU2AdjacentFinePairOrbitVector_zero
#print axioms physicalYangMillsSU2AdjacentFinePairFrozenCouplingStepVector_zero

end

end MGAP4D.MathlibAnalytic
