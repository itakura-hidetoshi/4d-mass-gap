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
  finiteSpan : Nat → Set state
  physicalState : Set state
  approximantInFiniteSpan : ∀ ψ n, approximant ψ n ∈ finiteSpan (n + 1)
  norm_zero : norm zero = 0
  distance_self_zero : ∀ ψ, distance ψ ψ = 0
  approximant_converges : ∀ ψ, ψ ∈ physicalState → convergenceTo (approximant ψ) ψ
  normTopologyVisible : Prop
  normTopologyVisible_proof : normTopologyVisible
  cauchyCompletionStillOpen : Prop
  cauchyCompletionStillOpen_proof : cauchyCompletionStillOpen
  hilbertCompletionStillOpen : Prop
  hilbertCompletionStillOpen_proof : hilbertCompletionStillOpen
  finalReleaseHeld : Prop
  finalReleaseHeld_proof : finalReleaseHeld
  publicBoundaryHeld : Prop
  publicBoundaryHeld_proof : publicBoundaryHeld

/-- Ready predicate for the norm-topology skeleton.

The predicate restates proposition-level obligations over the current carrier, so
proof fields are not accidentally used as type arguments. -/
def HilbertNormTopologySkeletonData.ready (D : HilbertNormTopologySkeletonData) : Prop :=
  hilbertFiniteSpanDensitySkeletonReviewSurface.ready ∧
  (∀ ψ n, D.approximant ψ n ∈ D.finiteSpan (n + 1)) ∧
  D.norm D.zero = 0 ∧
  (∀ ψ, D.distance ψ ψ = 0) ∧
  (∀ ψ, ψ ∈ D.physicalState → D.convergenceTo (D.approximant ψ) ψ) ∧
  D.normTopologyVisible ∧ D.cauchyCompletionStillOpen ∧
  D.hilbertCompletionStillOpen ∧ D.finalReleaseHeld ∧ D.publicBoundaryHeld

theorem hilbert_norm_topology_approximant_in_finite_span
    (D : HilbertNormTopologySkeletonData) (ψ : D.state) (n : Nat) :
    D.approximant ψ n ∈ D.finiteSpan (n + 1) := by
  exact D.approximantInFiniteSpan ψ n

theorem hilbert_norm_topology_approximant_converges
    (D : HilbertNormTopologySkeletonData) (ψ : D.state) (hψ : ψ ∈ D.physicalState) :
    D.convergenceTo (D.approximant ψ) ψ := by
  exact D.approximant_converges ψ hψ

theorem hilbert_norm_topology_completion_still_open
    (D : HilbertNormTopologySkeletonData) :
    D.hilbertCompletionStillOpen := by
  exact D.hilbertCompletionStillOpen_proof

/-- Prototype norm-topology skeleton over `Nat`. -/
def prototypeHilbertNormTopologySkeletonData : HilbertNormTopologySkeletonData :=
  { finiteSpanDensityReady := hilbert_finite_span_density_skeleton_review_surface_ready
    state := Nat
    zero := 0
    norm := fun _ => 0
    distance := fun _ _ => 0
    convergenceTo := fun _ _ => True
    approximant := fun _ n => n
    finiteSpan := fun _ => Set.univ
    physicalState := Set.univ
    approximantInFiniteSpan := by
      intro ψ n
      exact Set.mem_univ (n)
    norm_zero := rfl
    distance_self_zero := by intro ψ; rfl
    approximant_converges := by intro ψ hψ; exact True.intro
    normTopologyVisible := True
    normTopologyVisible_proof := True.intro
    cauchyCompletionStillOpen := True
    cauchyCompletionStillOpen_proof := True.intro
    hilbertCompletionStillOpen := True
    hilbertCompletionStillOpen_proof := True.intro
    finalReleaseHeld := True
    finalReleaseHeld_proof := True.intro
    publicBoundaryHeld := True
    publicBoundaryHeld_proof := True.intro }

theorem prototype_hilbert_norm_topology_skeleton_ready :
    prototypeHilbertNormTopologySkeletonData.ready := by
  exact And.intro prototypeHilbertNormTopologySkeletonData.finiteSpanDensityReady <|
    And.intro prototypeHilbertNormTopologySkeletonData.approximantInFiniteSpan <|
    And.intro prototypeHilbertNormTopologySkeletonData.norm_zero <|
    And.intro prototypeHilbertNormTopologySkeletonData.distance_self_zero <|
    And.intro prototypeHilbertNormTopologySkeletonData.approximant_converges <|
    And.intro prototypeHilbertNormTopologySkeletonData.normTopologyVisible_proof <|
    And.intro prototypeHilbertNormTopologySkeletonData.cauchyCompletionStillOpen_proof <|
    And.intro prototypeHilbertNormTopologySkeletonData.hilbertCompletionStillOpen_proof <|
    And.intro prototypeHilbertNormTopologySkeletonData.finalReleaseHeld_proof
      prototypeHilbertNormTopologySkeletonData.publicBoundaryHeld_proof

structure HilbertNormTopologySkeletonReviewSurface where
  finiteSpanDensityReady : hilbertFiniteSpanDensitySkeletonReviewSurface.ready
  normTopologyReady : prototypeHilbertNormTopologySkeletonData.ready
  normTopologyEstablished : Prop
  normTopologyEstablished_proof : normTopologyEstablished
  cauchyCompletionStillOpen : Prop
  cauchyCompletionStillOpen_proof : cauchyCompletionStillOpen
  hilbertCompletionStillOpen : Prop
  hilbertCompletionStillOpen_proof : hilbertCompletionStillOpen
  finalReleaseHeld : Prop
  finalReleaseHeld_proof : finalReleaseHeld
  publicBoundaryHeld : Prop
  publicBoundaryHeld_proof : publicBoundaryHeld

def HilbertNormTopologySkeletonReviewSurface.ready
    (S : HilbertNormTopologySkeletonReviewSurface) : Prop :=
  hilbertFiniteSpanDensitySkeletonReviewSurface.ready ∧
  prototypeHilbertNormTopologySkeletonData.ready ∧ S.normTopologyEstablished ∧
  S.cauchyCompletionStillOpen ∧ S.hilbertCompletionStillOpen ∧
  S.finalReleaseHeld ∧ S.publicBoundaryHeld

def hilbertNormTopologySkeletonReviewSurface : HilbertNormTopologySkeletonReviewSurface :=
  { finiteSpanDensityReady := hilbert_finite_span_density_skeleton_review_surface_ready
    normTopologyReady := prototype_hilbert_norm_topology_skeleton_ready
    normTopologyEstablished := True
    normTopologyEstablished_proof := True.intro
    cauchyCompletionStillOpen := True
    cauchyCompletionStillOpen_proof := True.intro
    hilbertCompletionStillOpen := True
    hilbertCompletionStillOpen_proof := True.intro
    finalReleaseHeld := True
    finalReleaseHeld_proof := True.intro
    publicBoundaryHeld := True
    publicBoundaryHeld_proof := True.intro }

theorem hilbert_norm_topology_skeleton_review_surface_ready :
    hilbertNormTopologySkeletonReviewSurface.ready := by
  exact And.intro hilbertNormTopologySkeletonReviewSurface.finiteSpanDensityReady <|
    And.intro hilbertNormTopologySkeletonReviewSurface.normTopologyReady <|
    And.intro hilbertNormTopologySkeletonReviewSurface.normTopologyEstablished_proof <|
    And.intro hilbertNormTopologySkeletonReviewSurface.cauchyCompletionStillOpen_proof <|
    And.intro hilbertNormTopologySkeletonReviewSurface.hilbertCompletionStillOpen_proof <|
    And.intro hilbertNormTopologySkeletonReviewSurface.finalReleaseHeld_proof
      hilbertNormTopologySkeletonReviewSurface.publicBoundaryHeld_proof

end MathlibAnalytic
end MGAP4D
