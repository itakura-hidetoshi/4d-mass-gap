import MGAP4D.MathlibAnalytic.InfiniteDimensionalHilbertNecessityFromPNP

namespace MGAP4D
namespace MathlibAnalytic

universe u

/-- Arbitrarily large distinguishable excitation family.

This strengthens the P≠NP-style Hilbert necessity bridge by extracting, from a
Nat-indexed distinguishable excitation family, a finite family of any requested
size.  This is the Lean-level surface that blocks replacing the physical
Hilbert realization by a bounded finite collapse model.

Boundary: this is an arbitrarily-large distinguishability surface, not yet a
full linear-independent Hilbert basis construction. -/
structure ArbitrarilyLargeHilbertExcitationFamilyData where
  pnpBridgeReady : infiniteDimensionalHilbertNecessityFromPNPReviewSurface.ready
  state : Type u
  excitation : Nat → state
  distinguishable : state → state → Prop
  pairwise_distinguishable : ∀ n m : Nat, n ≠ m →
    distinguishable (excitation n) (excitation m)
  finite_family : (k : Nat) → Fin k → state
  finite_family_def : ∀ k i, finite_family k i = excitation i.val
  finite_family_pairwise_distinguishable : ∀ k (i j : Fin k), i ≠ j →
    distinguishable (finite_family k i) (finite_family k j)
  arbitrarilyLargeFamilyVisible : Prop
  arbitrarilyLargeFamilyVisible_proof : arbitrarilyLargeFamilyVisible
  boundedFiniteCollapseBlocked : Prop
  boundedFiniteCollapseBlocked_proof : boundedFiniteCollapseBlocked
  fullLinearIndependenceStillOpen : Prop
  fullLinearIndependenceStillOpen_proof : fullLinearIndependenceStillOpen
  finalReleaseHeld : Prop
  finalReleaseHeld_proof : finalReleaseHeld
  publicBoundaryHeld : Prop
  publicBoundaryHeld_proof : publicBoundaryHeld

/-- Ready predicate for arbitrarily-large excitation families. -/
def ArbitrarilyLargeHilbertExcitationFamilyData.ready
    (D : ArbitrarilyLargeHilbertExcitationFamilyData) : Prop :=
  infiniteDimensionalHilbertNecessityFromPNPReviewSurface.ready ∧
  (∀ n m : Nat, n ≠ m → D.distinguishable (D.excitation n) (D.excitation m)) ∧
  (∀ k i, D.finite_family k i = D.excitation i.val) ∧
  (∀ k (i j : Fin k), i ≠ j →
    D.distinguishable (D.finite_family k i) (D.finite_family k j)) ∧
  D.arbitrarilyLargeFamilyVisible ∧
  D.boundedFiniteCollapseBlocked ∧
  D.fullLinearIndependenceStillOpen ∧
  D.finalReleaseHeld ∧ D.publicBoundaryHeld

/-- Extract a finite distinguishable family of any requested size. -/
theorem arbitrarily_large_hilbert_excitation_family_pairwise
    (D : ArbitrarilyLargeHilbertExcitationFamilyData)
    (k : Nat) (i j : Fin k) (hij : i ≠ j) :
    D.distinguishable (D.finite_family k i) (D.finite_family k j) := by
  exact D.finite_family_pairwise_distinguishable k i j hij

/-- Bounded finite collapse remains blocked by the arbitrarily large family. -/
theorem arbitrarily_large_hilbert_excitation_bounded_collapse_blocked
    (D : ArbitrarilyLargeHilbertExcitationFamilyData) :
    D.boundedFiniteCollapseBlocked := by
  exact D.boundedFiniteCollapseBlocked_proof

/-- Full linear-independence construction remains a visible next residual. -/
theorem arbitrarily_large_hilbert_excitation_linear_independence_still_open
    (D : ArbitrarilyLargeHilbertExcitationFamilyData) :
    D.fullLinearIndependenceStillOpen := by
  exact D.fullLinearIndependenceStillOpen_proof

/-- Final release remains held at this review boundary. -/
theorem arbitrarily_large_hilbert_excitation_final_release_held
    (D : ArbitrarilyLargeHilbertExcitationFamilyData) :
    D.finalReleaseHeld := by
  exact D.finalReleaseHeld_proof

/-- Prototype arbitrarily-large excitation family, using `Nat` as the candidate
state family and inequality as distinguishability. -/
noncomputable def prototypeArbitrarilyLargeHilbertExcitationFamilyData :
    ArbitrarilyLargeHilbertExcitationFamilyData.{0} :=
  { pnpBridgeReady := infinite_dimensional_hilbert_necessity_from_pnp_review_surface_ready
    state := Nat
    excitation := fun n => n
    distinguishable := fun a b => a ≠ b
    pairwise_distinguishable := by
      intro n m h
      exact h
    finite_family := fun k i => i.val
    finite_family_def := by
      intro k i
      rfl
    finite_family_pairwise_distinguishable := by
      intro k i j hij
      dsimp
      intro hval
      exact hij (Fin.ext hval)
    arbitrarilyLargeFamilyVisible :=
      infiniteDimensionalHilbertNecessityFromPNPReviewSurface.ready ∧
      infiniteDimensionalHilbertNecessityFromPNPReviewSurface.infiniteDimensionalNecessityEstablished
    arbitrarilyLargeFamilyVisible_proof :=
      And.intro infinite_dimensional_hilbert_necessity_from_pnp_review_surface_ready
        infinite_dimensional_hilbert_necessity_from_pnp_review_surface_ready.2.2.2.2.2.2.1
    boundedFiniteCollapseBlocked :=
      prototypeInfiniteDimensionalHilbertNecessityFromPNPData.finiteCertificateCollapseBlocked
    boundedFiniteCollapseBlocked_proof :=
      infinite_dimensional_hilbert_necessity_from_pnp_review_surface_ready.2.2.2.1
    fullLinearIndependenceStillOpen :=
      infiniteDimensionalHilbertNecessityFromPNPReviewSurface.fullInfiniteDimensionalConstructionStillOpen
    fullLinearIndependenceStillOpen_proof :=
      infinite_dimensional_hilbert_necessity_from_pnp_review_surface_ready.2.2.2.2.2.2.2.1
    finalReleaseHeld :=
      infiniteDimensionalHilbertNecessityFromPNPReviewSurface.finalReleaseHeld
    finalReleaseHeld_proof :=
      infinite_dimensional_hilbert_necessity_from_pnp_review_surface_ready.2.2.2.2.2.2.2.2.1
    publicBoundaryHeld :=
      infiniteDimensionalHilbertNecessityFromPNPReviewSurface.publicBoundaryHeld
    publicBoundaryHeld_proof :=
      infinite_dimensional_hilbert_necessity_from_pnp_review_surface_ready.2.2.2.2.2.2.2.2.2 }

theorem prototype_arbitrarily_large_hilbert_excitation_family_ready :
    prototypeArbitrarilyLargeHilbertExcitationFamilyData.ready := by
  exact And.intro infinite_dimensional_hilbert_necessity_from_pnp_review_surface_ready <|
    And.intro (by intro n m h; exact h) <|
    And.intro (by intro k i; rfl) <|
    And.intro prototypeArbitrarilyLargeHilbertExcitationFamilyData.finite_family_pairwise_distinguishable <|
    And.intro prototypeArbitrarilyLargeHilbertExcitationFamilyData.arbitrarilyLargeFamilyVisible_proof <|
    And.intro prototypeArbitrarilyLargeHilbertExcitationFamilyData.boundedFiniteCollapseBlocked_proof <|
    And.intro prototypeArbitrarilyLargeHilbertExcitationFamilyData.fullLinearIndependenceStillOpen_proof <|
    And.intro prototypeArbitrarilyLargeHilbertExcitationFamilyData.finalReleaseHeld_proof
      prototypeArbitrarilyLargeHilbertExcitationFamilyData.publicBoundaryHeld_proof

theorem prototype_arbitrarily_large_hilbert_excitation_family_pairwise
    (k : Nat) (i j : Fin k) (hij : i ≠ j) :
    prototypeArbitrarilyLargeHilbertExcitationFamilyData.distinguishable
      (prototypeArbitrarilyLargeHilbertExcitationFamilyData.finite_family k i)
      (prototypeArbitrarilyLargeHilbertExcitationFamilyData.finite_family k j) := by
  exact prototypeArbitrarilyLargeHilbertExcitationFamilyData.finite_family_pairwise_distinguishable
    k i j hij

/-- Review surface for arbitrarily-large distinguishable Hilbert excitation
families. -/
structure ArbitrarilyLargeHilbertExcitationFamilyReviewSurface where
  pnpBridgeReady : infiniteDimensionalHilbertNecessityFromPNPReviewSurface.ready
  largeFamilyReady : prototypeArbitrarilyLargeHilbertExcitationFamilyData.ready
  pairwiseFiniteFamily : ∀ k (i j : Fin k), i ≠ j →
    prototypeArbitrarilyLargeHilbertExcitationFamilyData.distinguishable
      (prototypeArbitrarilyLargeHilbertExcitationFamilyData.finite_family k i)
      (prototypeArbitrarilyLargeHilbertExcitationFamilyData.finite_family k j)
  boundedFiniteCollapseBlocked :
    prototypeArbitrarilyLargeHilbertExcitationFamilyData.boundedFiniteCollapseBlocked
  arbitrarilyLargeFamilyEstablished : Prop
  arbitrarilyLargeFamilyEstablished_proof : arbitrarilyLargeFamilyEstablished
  fullLinearIndependenceStillOpen : Prop
  fullLinearIndependenceStillOpen_proof : fullLinearIndependenceStillOpen
  finalReleaseHeld : Prop
  finalReleaseHeld_proof : finalReleaseHeld
  publicBoundaryHeld : Prop
  publicBoundaryHeld_proof : publicBoundaryHeld

def ArbitrarilyLargeHilbertExcitationFamilyReviewSurface.ready
    (S : ArbitrarilyLargeHilbertExcitationFamilyReviewSurface) : Prop :=
  infiniteDimensionalHilbertNecessityFromPNPReviewSurface.ready ∧
  prototypeArbitrarilyLargeHilbertExcitationFamilyData.ready ∧
  (∀ k (i j : Fin k), i ≠ j →
    prototypeArbitrarilyLargeHilbertExcitationFamilyData.distinguishable
      (prototypeArbitrarilyLargeHilbertExcitationFamilyData.finite_family k i)
      (prototypeArbitrarilyLargeHilbertExcitationFamilyData.finite_family k j)) ∧
  prototypeArbitrarilyLargeHilbertExcitationFamilyData.boundedFiniteCollapseBlocked ∧
  S.arbitrarilyLargeFamilyEstablished ∧
  S.fullLinearIndependenceStillOpen ∧ S.finalReleaseHeld ∧ S.publicBoundaryHeld

noncomputable def arbitrarilyLargeHilbertExcitationFamilyReviewSurface :
    ArbitrarilyLargeHilbertExcitationFamilyReviewSurface :=
  { pnpBridgeReady := infinite_dimensional_hilbert_necessity_from_pnp_review_surface_ready
    largeFamilyReady := prototype_arbitrarily_large_hilbert_excitation_family_ready
    pairwiseFiniteFamily := prototype_arbitrarily_large_hilbert_excitation_family_pairwise
    boundedFiniteCollapseBlocked := prototypeArbitrarilyLargeHilbertExcitationFamilyData.boundedFiniteCollapseBlocked_proof
    arbitrarilyLargeFamilyEstablished := prototypeArbitrarilyLargeHilbertExcitationFamilyData.ready
    arbitrarilyLargeFamilyEstablished_proof := prototype_arbitrarily_large_hilbert_excitation_family_ready
    fullLinearIndependenceStillOpen := prototypeArbitrarilyLargeHilbertExcitationFamilyData.fullLinearIndependenceStillOpen
    fullLinearIndependenceStillOpen_proof := prototypeArbitrarilyLargeHilbertExcitationFamilyData.fullLinearIndependenceStillOpen_proof
    finalReleaseHeld := prototypeArbitrarilyLargeHilbertExcitationFamilyData.finalReleaseHeld
    finalReleaseHeld_proof := prototypeArbitrarilyLargeHilbertExcitationFamilyData.finalReleaseHeld_proof
    publicBoundaryHeld := prototypeArbitrarilyLargeHilbertExcitationFamilyData.publicBoundaryHeld
    publicBoundaryHeld_proof := prototypeArbitrarilyLargeHilbertExcitationFamilyData.publicBoundaryHeld_proof }

theorem arbitrarily_large_hilbert_excitation_family_review_surface_ready :
    arbitrarilyLargeHilbertExcitationFamilyReviewSurface.ready := by
  exact And.intro infinite_dimensional_hilbert_necessity_from_pnp_review_surface_ready <|
    And.intro prototype_arbitrarily_large_hilbert_excitation_family_ready <|
    And.intro prototype_arbitrarily_large_hilbert_excitation_family_pairwise <|
    And.intro prototypeArbitrarilyLargeHilbertExcitationFamilyData.boundedFiniteCollapseBlocked_proof <|
    And.intro arbitrarilyLargeHilbertExcitationFamilyReviewSurface.arbitrarilyLargeFamilyEstablished_proof <|
    And.intro arbitrarilyLargeHilbertExcitationFamilyReviewSurface.fullLinearIndependenceStillOpen_proof <|
    And.intro arbitrarilyLargeHilbertExcitationFamilyReviewSurface.finalReleaseHeld_proof
      arbitrarilyLargeHilbertExcitationFamilyReviewSurface.publicBoundaryHeld_proof

theorem arbitrarily_large_hilbert_excitation_family_final_release_held :
    ArbitrarilyLargeHilbertExcitationFamilyReviewSurface.finalReleaseHeld
      arbitrarilyLargeHilbertExcitationFamilyReviewSurface := by
  exact arbitrarilyLargeHilbertExcitationFamilyReviewSurface.finalReleaseHeld_proof

end MathlibAnalytic
end MGAP4D