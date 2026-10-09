import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarUncenteredPosteriorCovarianceSchur
import Mathlib.Tactic

/-!
# P4-Q2: original joint conditional-covariance identity for the true Gram

PR #5321 keeps signed, exact pair-Haar transported posterior residual
covariances of the *uncentered* fine right Krylov orbit. Here we go one
step deeper: these are not merely formal pair-Haar inner products.
Under the canonical ORIGINAL Wilson joint law μ_beta, the original
half-density isometry U_beta transports the true one-link projection to
the genuine CondExpL2 operator P_beta,e.

For any pair-Haar vectors v,w, prove exactly

  ⟪v-Q_e v, w-Q_e w⟫
     = ⟪U_beta v,U_beta w⟫
       - ⟪P_beta,e U_beta v,P_beta,e U_beta w⟫.

The difference is the original conditional covariance loss and is proved
from native mathlib CondExpL2 orthogonality, not any surrogate posterior.
Applied to the actual physical uncentered right-Krylov receivers at
the frozen beta(n), the signed link covariance of #5321 has precisely
this original-joint representation, with fine beta(n+1) retained in
the orbit. This identity exposes cancellations in the unbounded-link
sum and permits future genuinely local conditional-covariance bounds.

No assertion of spatial volume uniformity, Dobrushin reconstruction,
new axiom, sorry/admit, or continuum mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 750000

/-- Sharp real cross-polarization identity for the NATIVE original
joint CondExpL2 projection, using retained test functions. -/
theorem realL2_condExp_residual_inner_eq_covarianceLoss
    {α : Type*} {m : MeasurableSpace α} [m0 : MeasurableSpace α]
    {μ : Measure α} (hm : m ≤ m0) (f g : Lp ℝ 2 μ) :
    inner ℝ (f - (condExpL2 (μ := μ) ℝ ℝ hm f).1)
      (g - (condExpL2 (μ := μ) ℝ ℝ hm g).1) =
    inner ℝ f g -
      inner ℝ ((condExpL2 (μ := μ) ℝ ℝ hm f).1)
        ((condExpL2 (μ := μ) ℝ ℝ hm g).1) := by
  let p : Lp ℝ 2 μ := (condExpL2 (μ := μ) ℝ ℝ hm f).1
  let q : Lp ℝ 2 μ := (condExpL2 (μ := μ) ℝ ℝ hm g).1
  have hp : AEStronglyMeasurable[m] (fun z => p z) μ :=
    aestronglyMeasurable_condExpL2 hm f
  have hq : AEStronglyMeasurable[m] (fun z => q z) μ :=
    aestronglyMeasurable_condExpL2 hm g
  have hfq : inner ℝ f q = inner ℝ p q :=
    inner_condExpL2_eq_inner_fun (𝕜 := ℝ) hm f q hq
  have hgp : inner ℝ g p = inner ℝ q p :=
    inner_condExpL2_eq_inner_fun (𝕜 := ℝ) hm g p hp
  have hpg : inner ℝ p g = inner ℝ p q := by
    calc
      inner ℝ p g = inner ℝ g p := real_inner_comm g p
      _ = inner ℝ q p := hgp
      _ = inner ℝ p q := real_inner_comm q p
  change inner ℝ (f - p) (g - q) =
    inner ℝ f g - inner ℝ p q
  calc
    inner ℝ (f - p) (g - q) =
        inner ℝ f g - inner ℝ f q -
          inner ℝ p g + inner ℝ p q := by
            rw [inner_sub_left, inner_sub_right, inner_sub_right]
            ring
    _ = inner ℝ f g - inner ℝ p q := by
      rw [hfq, hpg]
      ring

local instance p4JointCovTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4JointCovCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4JointCovSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4JointCovMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4JointCovBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4JointCovLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Exact original joint conditional-covariance loss behind every
transported pair-Haar residual covariance. U_beta is the authentic
Wilson ground-state half-density isometry and P_e is its ORIGINAL
joint-law conditional expectation. -/
theorem pairHaarTransportedGroundStateSpatialLinkProjection_residualInner_eq_jointCondExpLoss
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (v w : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) :
    let U :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
        H N hN beta hbeta
    let P :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
        H N hN beta hbeta e
    inner ℝ (v - pairHaarTransportedGroundStateSpatialLinkProjection
        H N hN beta hbeta e v)
      (w - pairHaarTransportedGroundStateSpatialLinkProjection
        H N hN beta hbeta e w) =
      inner ℝ (U v) (U w) - inner ℝ (P (U v)) (P (U w)) := by
  let U :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
      H N hN beta hbeta
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
      H N hN beta hbeta e
  let Q := pairHaarTransportedGroundStateSpatialLinkProjection
    H N hN beta hbeta e
  let hm := periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace_le
    H N e
  have hQv : Q v = U.symm (P (U v)) := rfl
  have hQw : Q w = U.symm (P (U w)) := rfl
  have hResV : U (v - Q v) = U v - P (U v) := by
    rw [map_sub, hQv, LinearIsometryEquiv.apply_symm_apply]
  have hResW : U (w - Q w) = U w - P (U w) := by
    rw [map_sub, hQw, LinearIsometryEquiv.apply_symm_apply]
  have hJoint :
      inner ℝ (U v - P (U v)) (U w - P (U w)) =
      inner ℝ (U v) (U w) -
        inner ℝ (P (U v)) (P (U w)) := by
    simpa only [P,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_apply]
      using (realL2_condExp_residual_inner_eq_covarianceLoss hm (U v) (U w))
  change inner ℝ (v - Q v) (w - Q w) =
    inner ℝ (U v) (U w) -
      inner ℝ (P (U v)) (P (U w))
  calc
    inner ℝ (v - Q v) (w - Q w) =
        inner ℝ (U (v - Q v)) (U (w - Q w)) := by
          exact (U.inner_map_map _ _).symm
    _ = inner ℝ (U v - P (U v)) (U w - P (U w)) := by
      rw [hResV, hResW]
    _ = inner ℝ (U v) (U w) -
          inner ℝ (P (U v)) (P (U w)) := hJoint

/-- Physical specialization: the signed posterior link covariance of
the true UN-CENTERED fine-right Krylov Gram is exactly an ORIGINAL
positive-beta Wilson joint-law conditional covariance loss. -/
theorem fineRightKrylovOriginalPosteriorLinkCovariance_eq_jointCondExpLoss
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ)
    (e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1)))
    (i j : Fin (r + 1)) :
    let H := halfExtent (n + 1)
    let U :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
        H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
    let P :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
        H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) e
    let v : Fin (r + 1) →
        PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H 2 :=
      fun k =>
        normalizedPhysicalOneSlabPairHaarReceiver
          H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
          (physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n (k : ℕ))
    fineRightKrylovOriginalPosteriorLinkCovariance
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e i j =
      inner ℝ (U (v i)) (U (v j)) -
        inner ℝ (P (U (v i))) (P (U (v j))) := by
  classical
  let H := halfExtent (n + 1)
  let v : Fin (r + 1) →
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H 2 :=
    fun k =>
      normalizedPhysicalOneSlabPairHaarReceiver
        H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
        (physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n (k : ℕ))
  simpa only [H, v, fineRightKrylovOriginalPosteriorLinkCovariance,
    fineRightKrylovOriginalPosteriorLinkResidual] using
    (pairHaarTransportedGroundStateSpatialLinkProjection_residualInner_eq_jointCondExpLoss
      H 2 specialUnitaryTwoWilsonRankPositive
      (beta n) (hbeta n) e (v i) (v j))

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
