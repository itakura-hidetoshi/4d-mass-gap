import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpatialSignedPermutationBoundaryStep

/-!
# Pullback action of abstract signed spatial permutations on gauge configurations

A general signed spatial symmetry acts on a positive physical edge by a signed boundary step, not
necessarily by another forward positive edge.  The canonical `periodicHypercubicStepValue` already
interprets such a step correctly: forward traversal reads `A e`, backward traversal reads `(A e)⁻¹`.

We therefore define the transformed configuration by pulling the requested positive edge back
through the inverse signed spatial symmetry and evaluating the original configuration on that signed
preimage:

`(g • A)(e) = periodicHypercubicStepValue A (I_{g⁻¹}(e))`.

Using the inverse gives the conventional left-action direction once composition is proved in a later
layer.  This file deliberately closes only the definition and the identity law.  Generator readback,
composition, plaquette-holonomy covariance, cubic-channel packaging, continuum spin, and spectral
claims remain separate additive obligations.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Pull a gauge configuration through an abstract signed spatial permutation.  Orientation reversal
is handled canonically by `periodicHypercubicStepValue`. -/
def periodicHypercubicConfigurationSpatialSignedPermutation
    {n : ℕ} {Gauge : Type} [Group Gauge]
    (g : SpatialSignedPermutationGroup)
    (A : PeriodicHypercubicEdge n → Gauge) :
    PeriodicHypercubicEdge n → Gauge :=
  fun e =>
    periodicHypercubicStepValue A
      (periodicHypercubicEdgeSpatialSignedPermutationBoundaryStep n g⁻¹ e)

/-- The identity signed spatial permutation sends every positive edge to that same edge with forward
orientation. -/
@[simp]
theorem periodicHypercubicEdgeSpatialSignedPermutationBoundaryStep_one
    (n : ℕ)
    (e : PeriodicHypercubicEdge n) :
    periodicHypercubicEdgeSpatialSignedPermutationBoundaryStep n 1 e =
      { edge := e, orientation := .forward } := by
  rcases e with ⟨x, μ⟩
  refine Fin.cases ?_ (fun k => ?_) μ
  · simp [periodicHypercubicEdgeSpatialSignedPermutationBoundaryStep]
  · simp [periodicHypercubicEdgeSpatialSignedPermutationBoundaryStep,
      periodicHypercubicSpatialSignedPermutationAxis]

/-- The configuration pullback has the correct identity action. -/
@[simp]
theorem periodicHypercubicConfigurationSpatialSignedPermutation_one
    {n : ℕ} {Gauge : Type} [Group Gauge]
    (A : PeriodicHypercubicEdge n → Gauge) :
    periodicHypercubicConfigurationSpatialSignedPermutation 1 A = A := by
  funext e
  simp [periodicHypercubicConfigurationSpatialSignedPermutation,
    periodicHypercubicStepValue]

/-- Pointwise identity receipt for audit-visible downstream rewriting. -/
@[simp]
theorem periodicHypercubicConfigurationSpatialSignedPermutation_one_apply
    {n : ℕ} {Gauge : Type} [Group Gauge]
    (A : PeriodicHypercubicEdge n → Gauge)
    (e : PeriodicHypercubicEdge n) :
    periodicHypercubicConfigurationSpatialSignedPermutation 1 A e = A e := by
  rw [periodicHypercubicConfigurationSpatialSignedPermutation_one]

end

end MathlibAnalytic
end MGAP4D
