import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonPlaquetteRandomScanVariationDecay
import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonCanonicalInfluenceSupport
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A Dobrushin matrix has active geometric support when every influence entry
outside the active plaquette-neighbor set vanishes. -/
structure FiniteOrientedLatticeWilsonDobrushinActiveSupport
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L) : Prop where
  influence_eq_zero_of_not_mem_active :
    ∀ target source : L.Edge,
      source ∉ L.activePlaquetteNeighbors target →
        D.influence target source = 0

/-- The exact canonical Dobrushin matrix carries the geometric active-support
certificate proved from plaquette locality. -/
def finiteOrientedLatticeWilsonCanonicalDobrushinActiveSupport
    (L : FiniteOrientedLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge)
    (hStrict : L.canonicalDobrushinCoefficient hEdge < 1) :
    FiniteOrientedLatticeWilsonDobrushinActiveSupport
      (finiteOrientedLatticeWilsonCanonicalDobrushinMatrixData
        L hEdge hStrict) :=
  { influence_eq_zero_of_not_mem_active := by
      intro target source hInactive
      change L.canonicalDobrushinInfluence target source = 0
      exact
        finite_oriented_canonicalDobrushinInfluence_eq_zero_of_not_mem_active
          L target source hInactive }

/-- One geometric support expansion keeps the current support and adds every
active plaquette neighbor of every supported physical link. -/
noncomputable def
    FiniteOrientedLatticeWilsonSystem.activePlaquetteNeighborExpansion
    (L : FiniteOrientedLatticeWilsonSystem)
    (seed : Finset L.Edge) : Finset L.Edge := by
  classical
  exact seed ∪ seed.biUnion L.activePlaquetteNeighbors

/-- The active plaquette-neighbor ball reached from `seed` in at most `k`
propagation steps. -/
noncomputable def
    FiniteOrientedLatticeWilsonSystem.activePlaquetteNeighborBall
    (L : FiniteOrientedLatticeWilsonSystem)
    (seed : Finset L.Edge) : ℕ → Finset L.Edge
  | 0 => seed
  | k + 1 =>
      L.activePlaquetteNeighborExpansion
        (L.activePlaquetteNeighborBall seed k)

@[simp] theorem finite_oriented_activePlaquetteNeighborBall_zero
    (L : FiniteOrientedLatticeWilsonSystem)
    (seed : Finset L.Edge) :
    L.activePlaquetteNeighborBall seed 0 = seed := rfl

@[simp] theorem finite_oriented_activePlaquetteNeighborBall_succ
    (L : FiniteOrientedLatticeWilsonSystem)
    (seed : Finset L.Edge)
    (k : ℕ) :
    L.activePlaquetteNeighborBall seed (k + 1) =
      L.activePlaquetteNeighborExpansion
        (L.activePlaquetteNeighborBall seed k) := rfl

/-- Membership in one support expansion is either retained membership or one
active plaquette-neighbor step from the previous support. -/
theorem finite_oriented_mem_activePlaquetteNeighborExpansion_iff
    (L : FiniteOrientedLatticeWilsonSystem)
    (seed : Finset L.Edge)
    (source : L.Edge) :
    source ∈ L.activePlaquetteNeighborExpansion seed ↔
      source ∈ seed ∨
        ∃ target ∈ seed,
          source ∈ L.activePlaquetteNeighbors target := by
  classical
  simp [FiniteOrientedLatticeWilsonSystem.activePlaquetteNeighborExpansion]

/-- If a variation is supported on `seed`, then one random-scan variation
update is supported on the one-step active plaquette-neighbor expansion. -/
theorem finiteOrientedConditionalAverageRandomScanVariation_eq_zero_of_support
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (S : FiniteOrientedLatticeWilsonDobrushinActiveSupport D)
    (variation : L.Edge → ℝ)
    (seed : Finset L.Edge)
    (hVariationSupport :
      ∀ e : L.Edge, e ∉ seed → variation e = 0)
    (source : L.Edge)
    (hSource :
      source ∉ L.activePlaquetteNeighborExpansion seed) :
    finiteOrientedConditionalAverageRandomScanVariation
      D variation source = 0 := by
  classical
  have hSourceSeed : source ∉ seed := by
    intro hMem
    apply hSource
    exact
      (finite_oriented_mem_activePlaquetteNeighborExpansion_iff
        L seed source).2 (Or.inl hMem)
  have hSourceVariation : variation source = 0 :=
    hVariationSupport source hSourceSeed
  have hSum :
      (∑ target : L.Edge,
        finiteOrientedConditionalAverageUpdatedVariation
          D variation target source) = 0 := by
    apply Finset.sum_eq_zero
    intro target _hTarget
    unfold finiteOrientedConditionalAverageUpdatedVariation
    by_cases hEq : source = target
    · simp [hEq]
    · by_cases hTargetSeed : target ∈ seed
      · have hNotActive :
            source ∉ L.activePlaquetteNeighbors target := by
          intro hActive
          apply hSource
          exact
            (finite_oriented_mem_activePlaquetteNeighborExpansion_iff
              L seed source).2
              (Or.inr ⟨target, hTargetSeed, hActive⟩)
        have hInfluence : D.influence target source = 0 :=
          S.influence_eq_zero_of_not_mem_active
            target source hNotActive
        simp [hEq, hSourceVariation, hInfluence]
      · have hTargetVariation : variation target = 0 :=
          hVariationSupport target hTargetSeed
        simp [hEq, hSourceVariation, hTargetVariation]
  unfold finiteOrientedConditionalAverageRandomScanVariation
  rw [hSum, mul_zero]

/-- Iterated random-scan variation cannot leave the active plaquette-neighbor
ball faster than one geometric support expansion per update. -/
theorem
    FiniteOrientedLatticeWilsonCenteredVariationProfile.randomScanConditionalAverageVariationIterate_eq_zero_of_not_mem_activeBall
    {L : FiniteOrientedLatticeWilsonSystem}
    {f : L.Configuration → ℝ}
    (P : FiniteOrientedLatticeWilsonCenteredVariationProfile L f)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (S : FiniteOrientedLatticeWilsonDobrushinActiveSupport D)
    (seed : Finset L.Edge)
    (hInitialSupport :
      ∀ source : L.Edge,
        source ∉ seed → P.variation source = 0)
    (k : ℕ)
    (source : L.Edge)
    (hSource :
      source ∉ L.activePlaquetteNeighborBall seed k) :
    P.randomScanConditionalAverageVariationIterate D k source = 0 := by
  induction k generalizing source with
  | zero =>
      simpa using hInitialSupport source hSource
  | succ k ih =>
      rw [
        FiniteOrientedLatticeWilsonCenteredVariationProfile.randomScanConditionalAverageVariationIterate_succ]
      apply
        finiteOrientedConditionalAverageRandomScanVariation_eq_zero_of_support
          D S
          (P.randomScanConditionalAverageVariationIterate D k)
          (L.activePlaquetteNeighborBall seed k)
      · intro e hOutside
        exact ih e hOutside
      · simpa using hSource

/-- The selected periodic `Z₂` plaquette variation remains supported inside the
active plaquette-neighbor ball grown from its distinct physical boundary links. -/
theorem
    z2PeriodicHypercubicOrientedPlaquetteRandomScanVariationIterate_eq_zero_of_not_mem_activeBall
    (n : ℕ) [NeZero n]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (p : PeriodicHypercubicPlaquette n)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData
      (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta))
    (S : FiniteOrientedLatticeWilsonDobrushinActiveSupport D)
    (k : ℕ)
    (source : PeriodicHypercubicEdge n)
    (hSource :
      source ∉
        FiniteOrientedLatticeWilsonSystem.activePlaquetteNeighborBall
          (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
          (periodicHypercubicPlaquetteEdges n p) k) :
    (z2PeriodicHypercubicOrientedPlaquetteCenteredVariationProfile
      n beta hBeta p).randomScanConditionalAverageVariationIterate
        D k source = 0 := by
  apply
    (z2PeriodicHypercubicOrientedPlaquetteCenteredVariationProfile
      n beta hBeta p)
      |>.randomScanConditionalAverageVariationIterate_eq_zero_of_not_mem_activeBall
        D S (periodicHypercubicPlaquetteEdges n p)
  · intro e hOutside
    rw [
      z2PeriodicHypercubicOrientedPlaquetteCenteredVariationProfile_variation,
      periodicHypercubicPlaquetteObservableLinkVariation_eq]
    exact if_neg hOutside
  · exact hSource

end

end MathlibAnalytic
end MGAP4D
