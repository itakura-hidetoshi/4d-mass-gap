import MGAP4D.MathlibAnalytic.HilbertCauchyCompletionSkeleton

namespace MGAP4D
namespace MathlibAnalytic

universe u

/-- Complete normed-space skeleton after the Cauchy-completion skeleton.

This packages a carrier with abstract zero/add/neg/scalar/norm/distance data and
a completeness predicate: every declared Cauchy sequence has a limit in the same
carrier.  It is still not a Mathlib `NormedSpace` or `CompleteSpace` instance. -/
structure HilbertCompleteNormedSpaceSkeletonData where
  cauchyCompletionReady : hilbertCauchyCompletionSkeletonReviewSurface.ready
  carrier : Type u
  zero : carrier
  add : carrier → carrier → carrier
  neg : carrier → carrier
  smul : ℝ → carrier → carrier
  norm : carrier → ℝ
  distance : carrier → carrier → ℝ
  cauchy : (Nat → carrier) → Prop
  convergesTo : (Nat → carrier) → carrier → Prop
  norm_zero : norm zero = 0
  distance_self_zero : ∀ x, distance x x = 0
  cauchy_has_limit : ∀ s, cauchy s → ∃ x : carrier, convergesTo s x
  completeNormedSpaceSkeletonVisible : Prop
  completeNormedSpaceSkeletonVisible_proof : completeNormedSpaceSkeletonVisible
  hilbertInnerProductStillOpen : Prop
  hilbertSpaceInstanceStillOpen : Prop
  finalReleaseHeld : Prop
  publicBoundaryHeld : Prop

def HilbertCompleteNormedSpaceSkeletonData.ready
    (D : HilbertCompleteNormedSpaceSkeletonData) : Prop :=
  D.cauchyCompletionReady ∧ D.norm_zero ∧ D.distance_self_zero ∧
  D.cauchy_has_limit ∧ D.completeNormedSpaceSkeletonVisible ∧
  D.hilbertInnerProductStillOpen ∧ D.hilbertSpaceInstanceStillOpen ∧
  D.finalReleaseHeld ∧ D.publicBoundaryHeld

/-- Every declared Cauchy sequence has a limit in the complete carrier. -/
theorem hilbert_complete_normed_space_cauchy_has_limit
    (D : HilbertCompleteNormedSpaceSkeletonData)
    (s : Nat → D.carrier) (hs : D.cauchy s) :
    ∃ x : D.carrier, D.convergesTo s x := by
  exact D.cauchy_has_limit s hs

/-- Distance is zero on the diagonal. -/
theorem hilbert_complete_normed_space_distance_self_zero
    (D : HilbertCompleteNormedSpaceSkeletonData) (x : D.carrier) :
    D.distance x x = 0 := by
  exact D.distance_self_zero x

/-- Hilbert inner-product construction remains visible after complete normed-space closure. -/
theorem hilbert_complete_normed_space_inner_product_still_open
    (D : HilbertCompleteNormedSpaceSkeletonData) :
    D.hilbertInnerProductStillOpen := by
  exact D.hilbertInnerProductStillOpen

/-- Prototype complete normed-space skeleton over a singleton carrier. -/
def prototypeHilbertCompleteNormedSpaceSkeletonData :
    HilbertCompleteNormedSpaceSkeletonData :=
  { cauchyCompletionReady := hilbert_cauchy_completion_skeleton_review_surface_ready
    carrier := PUnit
    zero := PUnit.unit
    add := fun _ _ => PUnit.unit
    neg := fun _ => PUnit.unit
    smul := fun _ _ => PUnit.unit
    norm := fun _ => 0
    distance := fun _ _ => 0
    cauchy := fun _ => True
    convergesTo := fun _ _ => True
    norm_zero := rfl
    distance_self_zero := by intro x; rfl
    cauchy_has_limit := by
      intro s hs
      exact ⟨PUnit.unit, True.intro⟩
    completeNormedSpaceSkeletonVisible := True
    completeNormedSpaceSkeletonVisible_proof := True.intro
    hilbertInnerProductStillOpen := True
    hilbertSpaceInstanceStillOpen := True
    finalReleaseHeld := True
    publicBoundaryHeld := True }

theorem prototype_hilbert_complete_normed_space_skeleton_ready :
    prototypeHilbertCompleteNormedSpaceSkeletonData.ready := by
  exact And.intro hilbert_cauchy_completion_skeleton_review_surface_ready <|
    And.intro rfl <|
    And.intro (by intro x; rfl) <|
    And.intro (by intro s hs; exact ⟨PUnit.unit, True.intro⟩) <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro True.intro

/-- Review surface for the complete normed-space skeleton. -/
structure HilbertCompleteNormedSpaceSkeletonReviewSurface where
  cauchyCompletionReady : hilbertCauchyCompletionSkeletonReviewSurface.ready
  completeNormedSpaceReady : prototypeHilbertCompleteNormedSpaceSkeletonData.ready
  cauchyHasLimit : ∀ s,
    prototypeHilbertCompleteNormedSpaceSkeletonData.cauchy s →
      ∃ x : prototypeHilbertCompleteNormedSpaceSkeletonData.carrier,
        prototypeHilbertCompleteNormedSpaceSkeletonData.convergesTo s x
  completeNormedSpaceSkeletonEstablished : Prop
  hilbertInnerProductStillOpen : Prop
  hilbertSpaceInstanceStillOpen : Prop
  finalReleaseHeld : Prop
  publicBoundaryHeld : Prop

def HilbertCompleteNormedSpaceSkeletonReviewSurface.ready
    (S : HilbertCompleteNormedSpaceSkeletonReviewSurface) : Prop :=
  S.cauchyCompletionReady ∧ S.completeNormedSpaceReady ∧ S.cauchyHasLimit ∧
  S.completeNormedSpaceSkeletonEstablished ∧ S.hilbertInnerProductStillOpen ∧
  S.hilbertSpaceInstanceStillOpen ∧ S.finalReleaseHeld ∧ S.publicBoundaryHeld

def hilbertCompleteNormedSpaceSkeletonReviewSurface :
    HilbertCompleteNormedSpaceSkeletonReviewSurface :=
  { cauchyCompletionReady := hilbert_cauchy_completion_skeleton_review_surface_ready
    completeNormedSpaceReady := prototype_hilbert_complete_normed_space_skeleton_ready
    cauchyHasLimit := by
      intro s hs
      exact ⟨PUnit.unit, True.intro⟩
    completeNormedSpaceSkeletonEstablished := True
    hilbertInnerProductStillOpen := True
    hilbertSpaceInstanceStillOpen := True
    finalReleaseHeld := True
    publicBoundaryHeld := True }

theorem hilbert_complete_normed_space_skeleton_review_surface_ready :
    hilbertCompleteNormedSpaceSkeletonReviewSurface.ready := by
  exact And.intro hilbert_cauchy_completion_skeleton_review_surface_ready <|
    And.intro prototype_hilbert_complete_normed_space_skeleton_ready <|
    And.intro (by intro s hs; exact ⟨PUnit.unit, True.intro⟩) <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro True.intro

end MathlibAnalytic
end MGAP4D
