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
  hilbertInnerProductStillOpen_proof : hilbertInnerProductStillOpen
  hilbertSpaceInstanceStillOpen : Prop
  hilbertSpaceInstanceStillOpen_proof : hilbertSpaceInstanceStillOpen
  finalReleaseHeld : Prop
  finalReleaseHeld_proof : finalReleaseHeld
  publicBoundaryHeld : Prop
  publicBoundaryHeld_proof : publicBoundaryHeld

/-- Ready predicate for the complete normed-space skeleton.

The predicate restates proposition-level obligations over the current carrier, so
proof fields are not accidentally used as type arguments. -/
def HilbertCompleteNormedSpaceSkeletonData.ready
    (D : HilbertCompleteNormedSpaceSkeletonData) : Prop :=
  hilbertCauchyCompletionSkeletonReviewSurface.ready ∧
  D.norm D.zero = 0 ∧
  (∀ x, D.distance x x = 0) ∧
  (∀ s, D.cauchy s → ∃ x : D.carrier, D.convergesTo s x) ∧
  D.completeNormedSpaceSkeletonVisible ∧
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
  exact D.hilbertInnerProductStillOpen_proof

/-- Prototype complete normed-space skeleton over a singleton carrier. -/
def prototypeHilbertCompleteNormedSpaceSkeletonData :
    HilbertCompleteNormedSpaceSkeletonData.{0} :=
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
    completeNormedSpaceSkeletonVisible :=
      hilbertCauchyCompletionSkeletonReviewSurface.ready ∧
      hilbertCauchyCompletionSkeletonReviewSurface.cauchyCompletionSkeletonEstablished
    completeNormedSpaceSkeletonVisible_proof :=
      And.intro hilbert_cauchy_completion_skeleton_review_surface_ready
        hilbertCauchyCompletionSkeletonReviewSurface.cauchyCompletionSkeletonEstablished_proof
    hilbertInnerProductStillOpen :=
      hilbertCauchyCompletionSkeletonReviewSurface.completeNormedSpaceStillOpen
    hilbertInnerProductStillOpen_proof :=
      hilbertCauchyCompletionSkeletonReviewSurface.completeNormedSpaceStillOpen_proof
    hilbertSpaceInstanceStillOpen :=
      hilbertCauchyCompletionSkeletonReviewSurface.hilbertSpaceInstanceStillOpen
    hilbertSpaceInstanceStillOpen_proof :=
      hilbertCauchyCompletionSkeletonReviewSurface.hilbertSpaceInstanceStillOpen_proof
    finalReleaseHeld := hilbertCauchyCompletionSkeletonReviewSurface.finalReleaseHeld
    finalReleaseHeld_proof := hilbertCauchyCompletionSkeletonReviewSurface.finalReleaseHeld_proof
    publicBoundaryHeld := hilbertCauchyCompletionSkeletonReviewSurface.publicBoundaryHeld
    publicBoundaryHeld_proof := hilbertCauchyCompletionSkeletonReviewSurface.publicBoundaryHeld_proof }

theorem prototype_hilbert_complete_normed_space_skeleton_ready :
    prototypeHilbertCompleteNormedSpaceSkeletonData.ready := by
  exact And.intro prototypeHilbertCompleteNormedSpaceSkeletonData.cauchyCompletionReady <|
    And.intro prototypeHilbertCompleteNormedSpaceSkeletonData.norm_zero <|
    And.intro prototypeHilbertCompleteNormedSpaceSkeletonData.distance_self_zero <|
    And.intro prototypeHilbertCompleteNormedSpaceSkeletonData.cauchy_has_limit <|
    And.intro prototypeHilbertCompleteNormedSpaceSkeletonData.completeNormedSpaceSkeletonVisible_proof <|
    And.intro prototypeHilbertCompleteNormedSpaceSkeletonData.hilbertInnerProductStillOpen_proof <|
    And.intro prototypeHilbertCompleteNormedSpaceSkeletonData.hilbertSpaceInstanceStillOpen_proof <|
    And.intro prototypeHilbertCompleteNormedSpaceSkeletonData.finalReleaseHeld_proof
      prototypeHilbertCompleteNormedSpaceSkeletonData.publicBoundaryHeld_proof

/-- Review surface for the complete normed-space skeleton. -/
structure HilbertCompleteNormedSpaceSkeletonReviewSurface where
  cauchyCompletionReady : hilbertCauchyCompletionSkeletonReviewSurface.ready
  completeNormedSpaceReady : prototypeHilbertCompleteNormedSpaceSkeletonData.ready
  cauchyHasLimit : Prop
  cauchyHasLimit_proof : cauchyHasLimit
  completeNormedSpaceSkeletonEstablished : Prop
  completeNormedSpaceSkeletonEstablished_proof : completeNormedSpaceSkeletonEstablished
  hilbertInnerProductStillOpen : Prop
  hilbertInnerProductStillOpen_proof : hilbertInnerProductStillOpen
  hilbertSpaceInstanceStillOpen : Prop
  hilbertSpaceInstanceStillOpen_proof : hilbertSpaceInstanceStillOpen
  finalReleaseHeld : Prop
  finalReleaseHeld_proof : finalReleaseHeld
  publicBoundaryHeld : Prop
  publicBoundaryHeld_proof : publicBoundaryHeld

def HilbertCompleteNormedSpaceSkeletonReviewSurface.ready
    (S : HilbertCompleteNormedSpaceSkeletonReviewSurface) : Prop :=
  hilbertCauchyCompletionSkeletonReviewSurface.ready ∧
  prototypeHilbertCompleteNormedSpaceSkeletonData.ready ∧ S.cauchyHasLimit ∧
  S.completeNormedSpaceSkeletonEstablished ∧ S.hilbertInnerProductStillOpen ∧
  S.hilbertSpaceInstanceStillOpen ∧ S.finalReleaseHeld ∧ S.publicBoundaryHeld

def hilbertCompleteNormedSpaceSkeletonReviewSurface :
    HilbertCompleteNormedSpaceSkeletonReviewSurface :=
  { cauchyCompletionReady := hilbert_cauchy_completion_skeleton_review_surface_ready
    completeNormedSpaceReady := prototype_hilbert_complete_normed_space_skeleton_ready
    cauchyHasLimit :=
      ∀ s,
        prototypeHilbertCompleteNormedSpaceSkeletonData.cauchy s →
          ∃ x : prototypeHilbertCompleteNormedSpaceSkeletonData.carrier,
            prototypeHilbertCompleteNormedSpaceSkeletonData.convergesTo s x
    cauchyHasLimit_proof := by
      intro s hs
      exact ⟨PUnit.unit, True.intro⟩
    completeNormedSpaceSkeletonEstablished := prototypeHilbertCompleteNormedSpaceSkeletonData.ready
    completeNormedSpaceSkeletonEstablished_proof := prototype_hilbert_complete_normed_space_skeleton_ready
    hilbertInnerProductStillOpen := prototypeHilbertCompleteNormedSpaceSkeletonData.hilbertInnerProductStillOpen
    hilbertInnerProductStillOpen_proof := prototypeHilbertCompleteNormedSpaceSkeletonData.hilbertInnerProductStillOpen_proof
    hilbertSpaceInstanceStillOpen := prototypeHilbertCompleteNormedSpaceSkeletonData.hilbertSpaceInstanceStillOpen
    hilbertSpaceInstanceStillOpen_proof := prototypeHilbertCompleteNormedSpaceSkeletonData.hilbertSpaceInstanceStillOpen_proof
    finalReleaseHeld := prototypeHilbertCompleteNormedSpaceSkeletonData.finalReleaseHeld
    finalReleaseHeld_proof := prototypeHilbertCompleteNormedSpaceSkeletonData.finalReleaseHeld_proof
    publicBoundaryHeld := prototypeHilbertCompleteNormedSpaceSkeletonData.publicBoundaryHeld
    publicBoundaryHeld_proof := prototypeHilbertCompleteNormedSpaceSkeletonData.publicBoundaryHeld_proof }

theorem hilbert_complete_normed_space_skeleton_review_surface_ready :
    hilbertCompleteNormedSpaceSkeletonReviewSurface.ready := by
  exact And.intro hilbertCompleteNormedSpaceSkeletonReviewSurface.cauchyCompletionReady <|
    And.intro hilbertCompleteNormedSpaceSkeletonReviewSurface.completeNormedSpaceReady <|
    And.intro hilbertCompleteNormedSpaceSkeletonReviewSurface.cauchyHasLimit_proof <|
    And.intro hilbertCompleteNormedSpaceSkeletonReviewSurface.completeNormedSpaceSkeletonEstablished_proof <|
    And.intro hilbertCompleteNormedSpaceSkeletonReviewSurface.hilbertInnerProductStillOpen_proof <|
    And.intro hilbertCompleteNormedSpaceSkeletonReviewSurface.hilbertSpaceInstanceStillOpen_proof <|
    And.intro hilbertCompleteNormedSpaceSkeletonReviewSurface.finalReleaseHeld_proof
      hilbertCompleteNormedSpaceSkeletonReviewSurface.publicBoundaryHeld_proof

end MathlibAnalytic
end MGAP4D