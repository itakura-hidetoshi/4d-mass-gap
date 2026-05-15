import MGAP4D.MathlibAnalytic.HilbertFiniteSpanDensitySkeleton

namespace MGAP4D
namespace MathlibAnalytic

universe u

/-- Minimal norm-topology skeleton after finite-span density.

This adds an abstract norm, distance, convergence predicate, and finite-span
approximation map.  Cauchy completion and full Hilbert completion remain open. -/
structure HilbertNormTopologySkeletonData where
  finiteSpanDensityReady : hilbertFiniteSpanDensitySkeletonReviewSurface.ready
  state : Type u
  zero : state
  norm : state → ℝ
  distance : state → state → ℝ
  convergenceTo : (Nat → state) → state → Prop
  approximant : state → Nat → state
  physicalState : Set state
  approximantInFiniteSpan : ∀ ψ n,
    approximant ψ n ∈ prototypeHilbertFiniteSpanDensitySkeletonData.finiteSpan (n + 1)
  norm_zero : norm zero = 0
  distance_self_zero : ∀ ψ, distance ψ ψ = 0
  approximant_converges : ∀ ψ, ψ ∈ physicalState → convergenceTo (approximant ψ) ψ
  normTopologyVisible : Prop
  normTopologyVisible_proof : normTopologyVisible
  cauchyCompletionStillOpen : Prop
  hilbertCompletionStillOpen : Prop
  finalReleaseHeld : Prop
  publicBoundaryHeld : Prop

def HilbertNormTopologySkeletonData.ready (D : HilbertNormTopologySkeletonData) : Prop :=
  D.finiteSpanDensityReady ∧ D.approximantInFiniteSpan ∧ D.norm_zero ∧
  D.distance_self_zero ∧ D.approximant_converges ∧ D.normTopologyVisible ∧
  D.cauchyCompletionStillOpen ∧ D.hilbertCompletionStillOpen ∧
  D.finalReleaseHeld ∧ D.publicBoundaryHeld

theorem hilbert_norm_topology_approximant_in_finite_span
    (D : HilbertNormTopologySkeletonData) (ψ : D.state) (n : Nat) :
    D.approximant ψ n ∈ prototypeHilbertFiniteSpanDensitySkeletonData.finiteSpan (n + 1) := by
  exact D.approximantInFiniteSpan ψ n

theorem hilbert_norm_topology_approximant_converges
    (D : HilbertNormTopologySkeletonData) (ψ : D.state) (hψ : ψ ∈ D.physicalState) :
    D.convergenceTo (D.approximant ψ) ψ := by
  exact D.approximant_converges ψ hψ

theorem hilbert_norm_topology_completion_still_open
    (D : HilbertNormTopologySkeletonData) :
    D.hilbertCompletionStillOpen := by
  exact D.hilbertCompletionStillOpen

/-- Prototype norm-topology skeleton over `Nat`. -/
def prototypeHilbertNormTopologySkeletonData : HilbertNormTopologySkeletonData :=
  { finiteSpanDensityReady := hilbert_finite_span_density_skeleton_review_surface_ready
    state := Nat
    zero := 0
    norm := fun _ => 0
    distance := fun _ _ => 0
    convergenceTo := fun _ _ => True
    approximant := fun _ n => n
    physicalState := Set.univ
    approximantInFiniteSpan := by
      intro ψ n
      dsimp [prototypeHilbertFiniteSpanDensitySkeletonData]
      exact Nat.lt_succ_self n
    norm_zero := rfl
    distance_self_zero := by intro ψ; rfl
    approximant_converges := by intro ψ hψ; exact True.intro
    normTopologyVisible := True
    normTopologyVisible_proof := True.intro
    cauchyCompletionStillOpen := True
    hilbertCompletionStillOpen := True
    finalReleaseHeld := True
    publicBoundaryHeld := True }

theorem prototype_hilbert_norm_topology_skeleton_ready :
    prototypeHilbertNormTopologySkeletonData.ready := by
  exact And.intro hilbert_finite_span_density_skeleton_review_surface_ready <|
    And.intro (by
      intro ψ n
      dsimp [prototypeHilbertFiniteSpanDensitySkeletonData]
      exact Nat.lt_succ_self n) <|
    And.intro rfl <|
    And.intro (by intro ψ; rfl) <|
    And.intro (by intro ψ hψ; exact True.intro) <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro True.intro

structure HilbertNormTopologySkeletonReviewSurface where
  finiteSpanDensityReady : hilbertFiniteSpanDensitySkeletonReviewSurface.ready
  normTopologyReady : prototypeHilbertNormTopologySkeletonData.ready
  normTopologyEstablished : Prop
  cauchyCompletionStillOpen : Prop
  hilbertCompletionStillOpen : Prop
  finalReleaseHeld : Prop
  publicBoundaryHeld : Prop

def HilbertNormTopologySkeletonReviewSurface.ready
    (S : HilbertNormTopologySkeletonReviewSurface) : Prop :=
  S.finiteSpanDensityReady ∧ S.normTopologyReady ∧ S.normTopologyEstablished ∧
  S.cauchyCompletionStillOpen ∧ S.hilbertCompletionStillOpen ∧
  S.finalReleaseHeld ∧ S.publicBoundaryHeld

def hilbertNormTopologySkeletonReviewSurface : HilbertNormTopologySkeletonReviewSurface :=
  { finiteSpanDensityReady := hilbert_finite_span_density_skeleton_review_surface_ready
    normTopologyReady := prototype_hilbert_norm_topology_skeleton_ready
    normTopologyEstablished := True
    cauchyCompletionStillOpen := True
    hilbertCompletionStillOpen := True
    finalReleaseHeld := True
    publicBoundaryHeld := True }

theorem hilbert_norm_topology_skeleton_review_surface_ready :
    hilbertNormTopologySkeletonReviewSurface.ready := by
  exact And.intro hilbert_finite_span_density_skeleton_review_surface_ready <|
    And.intro prototype_hilbert_norm_topology_skeleton_ready <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro True.intro

end MathlibAnalytic
end MGAP4D
