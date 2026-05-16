import MGAP4D.MathlibAnalytic.HilbertLinearIndependenceFromExcitations

namespace MGAP4D
namespace MathlibAnalytic

universe u

/-- Countable Hilbert-basis skeleton extracted from the finite
linear-independence excitation surface.

The previous layer established an arbitrary finite linearly-independent family.
This layer packages the next bridge: a `Nat`-indexed countable basis skeleton
whose every finite restriction is abstractly linearly independent.

Boundary: this is a countable basis skeleton only.  It does not yet construct a
completed Hilbert space, a norm topology, density of finite spans, or an
orthonormal basis in Mathlib's analytic sense. -/
structure HilbertCountableBasisSkeletonData where
  finiteIndependenceReady : hilbertLinearIndependenceFromExcitationsReviewSurface.ready
  state : Type u
  basisVector : Nat → state
  finiteBasisFamily : (k : Nat) → Fin k → state
  finiteBasisFamily_def : ∀ k (i : Fin k), finiteBasisFamily k i = basisVector i.val
  linearIndependent : (k : Nat) → (Fin k → state) → Prop
  finite_restrictions_linearly_independent : ∀ k,
    linearIndependent k (finiteBasisFamily k)
  countableBasisSkeletonVisible : Prop
  countableBasisSkeletonVisible_proof : countableBasisSkeletonVisible
  finiteSpanDensityStillOpen : Prop
  finiteSpanDensityStillOpen_proof : finiteSpanDensityStillOpen
  normTopologyStillOpen : Prop
  normTopologyStillOpen_proof : normTopologyStillOpen
  hilbertCompletionStillOpen : Prop
  hilbertCompletionStillOpen_proof : hilbertCompletionStillOpen
  finalReleaseHeld : Prop
  finalReleaseHeld_proof : finalReleaseHeld
  publicBoundaryHeld : Prop
  publicBoundaryHeld_proof : publicBoundaryHeld

/-- Ready predicate for the countable basis skeleton.

The predicate restates the proposition-level obligations.  Proof fields in the
structure are used only as witnesses when proving this predicate. -/
def HilbertCountableBasisSkeletonData.ready
    (D : HilbertCountableBasisSkeletonData) : Prop :=
  hilbertLinearIndependenceFromExcitationsReviewSurface.ready ∧
  (∀ k (i : Fin k), D.finiteBasisFamily k i = D.basisVector i.val) ∧
  (∀ k, D.linearIndependent k (D.finiteBasisFamily k)) ∧
  D.countableBasisSkeletonVisible ∧ D.finiteSpanDensityStillOpen ∧
  D.normTopologyStillOpen ∧ D.hilbertCompletionStillOpen ∧
  D.finalReleaseHeld ∧ D.publicBoundaryHeld

/-- Every finite restriction of the countable basis skeleton is abstractly
linearly independent. -/
theorem hilbert_countable_basis_finite_restriction_linearly_independent
    (D : HilbertCountableBasisSkeletonData) (k : Nat) :
    D.linearIndependent k (D.finiteBasisFamily k) := by
  exact D.finite_restrictions_linearly_independent k

/-- The finite basis family is exactly the restriction of the countable basis
skeleton. -/
theorem hilbert_countable_basis_finite_family_def
    (D : HilbertCountableBasisSkeletonData) (k : Nat) (i : Fin k) :
    D.finiteBasisFamily k i = D.basisVector i.val := by
  exact D.finiteBasisFamily_def k i

/-- Finite-span density is still a visible residual. -/
theorem hilbert_countable_basis_finite_span_density_still_open
    (D : HilbertCountableBasisSkeletonData) :
    D.finiteSpanDensityStillOpen := by
  exact D.finiteSpanDensityStillOpen_proof

/-- Hilbert completion is still a visible residual. -/
theorem hilbert_countable_basis_completion_still_open
    (D : HilbertCountableBasisSkeletonData) :
    D.hilbertCompletionStillOpen := by
  exact D.hilbertCompletionStillOpen_proof

/-- Prototype countable basis skeleton.

Here `state = Nat`, `basisVector n = n`, and abstract finite linear independence
is implemented as injectivity of each finite restriction. -/
def prototypeHilbertCountableBasisSkeletonData : HilbertCountableBasisSkeletonData :=
  { finiteIndependenceReady := hilbert_linear_independence_from_excitations_review_surface_ready
    state := Nat
    basisVector := fun n => n
    finiteBasisFamily := fun _ i => i.val
    finiteBasisFamily_def := by
      intro k i
      rfl
    linearIndependent := fun k family => ∀ i j : Fin k, family i = family j → i = j
    finite_restrictions_linearly_independent := by
      intro k i j h
      exact Fin.ext h
    countableBasisSkeletonVisible := True
    countableBasisSkeletonVisible_proof := True.intro
    finiteSpanDensityStillOpen := True
    finiteSpanDensityStillOpen_proof := True.intro
    normTopologyStillOpen := True
    normTopologyStillOpen_proof := True.intro
    hilbertCompletionStillOpen := True
    hilbertCompletionStillOpen_proof := True.intro
    finalReleaseHeld := True
    finalReleaseHeld_proof := True.intro
    publicBoundaryHeld := True
    publicBoundaryHeld_proof := True.intro }

theorem prototype_hilbert_countable_basis_skeleton_ready :
    prototypeHilbertCountableBasisSkeletonData.ready := by
  exact And.intro prototypeHilbertCountableBasisSkeletonData.finiteIndependenceReady <|
    And.intro prototypeHilbertCountableBasisSkeletonData.finiteBasisFamily_def <|
    And.intro prototypeHilbertCountableBasisSkeletonData.finite_restrictions_linearly_independent <|
    And.intro prototypeHilbertCountableBasisSkeletonData.countableBasisSkeletonVisible_proof <|
    And.intro prototypeHilbertCountableBasisSkeletonData.finiteSpanDensityStillOpen_proof <|
    And.intro prototypeHilbertCountableBasisSkeletonData.normTopologyStillOpen_proof <|
    And.intro prototypeHilbertCountableBasisSkeletonData.hilbertCompletionStillOpen_proof <|
    And.intro prototypeHilbertCountableBasisSkeletonData.finalReleaseHeld_proof
      prototypeHilbertCountableBasisSkeletonData.publicBoundaryHeld_proof

theorem prototype_hilbert_countable_basis_finite_restriction_linearly_independent
    (k : Nat) :
    prototypeHilbertCountableBasisSkeletonData.linearIndependent k
      (prototypeHilbertCountableBasisSkeletonData.finiteBasisFamily k) := by
  exact prototypeHilbertCountableBasisSkeletonData.finite_restrictions_linearly_independent k

/-- Review surface for the countable Hilbert-basis skeleton. -/
structure HilbertCountableBasisSkeletonReviewSurface where
  finiteIndependenceReady : hilbertLinearIndependenceFromExcitationsReviewSurface.ready
  countableBasisSkeletonReady : prototypeHilbertCountableBasisSkeletonData.ready
  finiteRestrictionIndependent : ∀ k,
    prototypeHilbertCountableBasisSkeletonData.linearIndependent k
      (prototypeHilbertCountableBasisSkeletonData.finiteBasisFamily k)
  countableBasisSkeletonEstablished : Prop
  countableBasisSkeletonEstablished_proof : countableBasisSkeletonEstablished
  finiteSpanDensityStillOpen : Prop
  finiteSpanDensityStillOpen_proof : finiteSpanDensityStillOpen
  normTopologyStillOpen : Prop
  normTopologyStillOpen_proof : normTopologyStillOpen
  hilbertCompletionStillOpen : Prop
  hilbertCompletionStillOpen_proof : hilbertCompletionStillOpen
  finalReleaseHeld : Prop
  finalReleaseHeld_proof : finalReleaseHeld
  publicBoundaryHeld : Prop
  publicBoundaryHeld_proof : publicBoundaryHeld

def HilbertCountableBasisSkeletonReviewSurface.ready
    (S : HilbertCountableBasisSkeletonReviewSurface) : Prop :=
  hilbertLinearIndependenceFromExcitationsReviewSurface.ready ∧
  prototypeHilbertCountableBasisSkeletonData.ready ∧
  (∀ k,
    prototypeHilbertCountableBasisSkeletonData.linearIndependent k
      (prototypeHilbertCountableBasisSkeletonData.finiteBasisFamily k)) ∧
  S.countableBasisSkeletonEstablished ∧ S.finiteSpanDensityStillOpen ∧
  S.normTopologyStillOpen ∧ S.hilbertCompletionStillOpen ∧
  S.finalReleaseHeld ∧ S.publicBoundaryHeld

def hilbertCountableBasisSkeletonReviewSurface : HilbertCountableBasisSkeletonReviewSurface :=
  { finiteIndependenceReady := hilbert_linear_independence_from_excitations_review_surface_ready
    countableBasisSkeletonReady := prototype_hilbert_countable_basis_skeleton_ready
    finiteRestrictionIndependent := prototype_hilbert_countable_basis_finite_restriction_linearly_independent
    countableBasisSkeletonEstablished := True
    countableBasisSkeletonEstablished_proof := True.intro
    finiteSpanDensityStillOpen := True
    finiteSpanDensityStillOpen_proof := True.intro
    normTopologyStillOpen := True
    normTopologyStillOpen_proof := True.intro
    hilbertCompletionStillOpen := True
    hilbertCompletionStillOpen_proof := True.intro
    finalReleaseHeld := True
    finalReleaseHeld_proof := True.intro
    publicBoundaryHeld := True
    publicBoundaryHeld_proof := True.intro }

theorem hilbert_countable_basis_skeleton_review_surface_ready :
    hilbertCountableBasisSkeletonReviewSurface.ready := by
  exact And.intro hilbertCountableBasisSkeletonReviewSurface.finiteIndependenceReady <|
    And.intro hilbertCountableBasisSkeletonReviewSurface.countableBasisSkeletonReady <|
    And.intro hilbertCountableBasisSkeletonReviewSurface.finiteRestrictionIndependent <|
    And.intro hilbertCountableBasisSkeletonReviewSurface.countableBasisSkeletonEstablished_proof <|
    And.intro hilbertCountableBasisSkeletonReviewSurface.finiteSpanDensityStillOpen_proof <|
    And.intro hilbertCountableBasisSkeletonReviewSurface.normTopologyStillOpen_proof <|
    And.intro hilbertCountableBasisSkeletonReviewSurface.hilbertCompletionStillOpen_proof <|
    And.intro hilbertCountableBasisSkeletonReviewSurface.finalReleaseHeld_proof
      hilbertCountableBasisSkeletonReviewSurface.publicBoundaryHeld_proof

theorem hilbert_countable_basis_skeleton_final_release_held :
    HilbertCountableBasisSkeletonReviewSurface.finalReleaseHeld
      hilbertCountableBasisSkeletonReviewSurface := by
  exact hilbertCountableBasisSkeletonReviewSurface.finalReleaseHeld_proof

end MathlibAnalytic
end MGAP4D
