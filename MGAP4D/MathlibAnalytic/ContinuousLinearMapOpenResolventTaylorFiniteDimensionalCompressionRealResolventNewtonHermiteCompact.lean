import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventNewtonHermiteTransfer
import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventStabilityCompact
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- The true Newton-Hermite interpolant together with its exact closed
remainder. -/
def continuousLinearMapRealResolventNewtonHermitePair
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (degree : ℕ) (A : V →L[ℝ] V)
    (nodes : Fin (degree + 1) → ℝ) (z : ℝ) :
    Fin 2 → (V →L[ℝ] V) :=
  ![continuousLinearMapRealResolventNewtonHermiteInterpolant degree A nodes z,
    continuousLinearMapRealResolventNewtonHermiteRemainder degree A nodes z]

/-- Specialization of the generic pair observable to a true real resolvent
tuple. -/
theorem continuousLinearMapRealResolventNewtonHermitePairObservable_eq
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (degree : ℕ) (A : V →L[ℝ] V)
    (nodes : Fin (degree + 1) → ℝ) (z : ℝ) :
    continuousLinearMapRealResolventNewtonHermitePairObservable
        degree nodes z
        (fun i => continuousLinearMapRealResolvent A
          (continuousLinearMapFinAppend nodes z i)) =
      continuousLinearMapRealResolventNewtonHermitePair
        degree A nodes z := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [continuousLinearMapRealResolventNewtonHermitePairObservable,
      continuousLinearMapRealResolventNewtonHermitePair,
      continuousLinearMapRealResolventNewtonHermiteInterpolant,
      continuousLinearMapFinAppend, Fin.init]
  · refine Fin.cases ?_ (fun j => Fin.elim0 j) j
    rfl

namespace ContinuousLinearMapOpenTaylorStrongLimitData

variable {α κ E V : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [FiniteDimensional ℝ V]

/-- Compact-uniform simultaneous convergence of Newton-Hermite interpolants
and their exact remainders for arbitrary finite node/evaluation families. -/
theorem iteratedDeriv_realResolventNewtonHermitePair_finiteDimensionalCompression_tendsto_uniformOn_compact_product
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (k degree : ℕ)
    (K : Set ℝ) (hKcompact : IsCompact K) {u : ℝ}
    (hKu : K ⊆ Set.Iic u) (hu : u < gap)
    (nodes : κ → Fin (degree + 1) → ℝ) (eval : κ → ℝ)
    (T : Set κ) (Z : Set ℝ)
    (hnodes : ∀ q ∈ T, ∀ j, nodes q j ∈ Z) (heval : ∀ q ∈ T, eval q ∈ Z)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ lambda ∈ K, ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k S.limitResolvent lambda)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ lambda ∈ K, ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q
        (_root_.iteratedDeriv k S.limitResolvent lambda)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l,
      ∀ lambda ∈ K, ∀ q ∈ T,
        ‖continuousLinearMapRealResolventNewtonHermitePair degree
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)) (nodes q) (eval q) -
          continuousLinearMapRealResolventNewtonHermitePair degree
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda))
            (nodes q) (eval q)‖ < epsilon := by
  let spectral : κ → Fin (degree + 2) → ℝ := fun q =>
    continuousLinearMapFinAppend (nodes q) (eval q)
  let R : α → (ℝ × κ) → Fin (degree + 2) → (V →L[ℝ] V) := fun a p j =>
    continuousLinearMapRealResolvent
      (continuousLinearMapCompression J Q
        (_root_.iteratedDeriv k (F a) p.1)) (spectral p.2 j)
  let R0 : (ℝ × κ) → Fin (degree + 2) → (V →L[ℝ] V) := fun p j =>
    continuousLinearMapRealResolvent
      (continuousLinearMapCompression J Q
        (_root_.iteratedDeriv k S.limitResolvent p.1)) (spectral p.2 j)
  have hspectral : ∀ q ∈ T, ∀ j, spectral q j ∈ Z := by
    intro q hq j
    refine Fin.lastCases ?_ (fun r => ?_) j
    · simpa [spectral] using heval q hq
    · simpa [spectral] using hnodes q hq r
  have hR0 : ∀ p ∈ K ×ˢ T, ∀ j, ‖R0 p j‖ ≤ M := by
    intro p hp j
    simpa [R0, continuousLinearMapRealResolventNorm] using
      hlimitNorm p.1 hp.1 (spectral p.2 j) (hspectral p.2 hp.2 j)
  have hR : ∀ eta : ℝ, 0 < eta →
      ∀ᶠ a in l, ∀ p ∈ K ×ˢ T, ∀ j, ‖R a p j - R0 p j‖ < eta := by
    intro eta heta
    have h :=
      S.iteratedDeriv_realResolvent_finiteDimensionalCompression_tendsto_uniformOn_compact_product
        B L hLgap hLresolvent J Q k K hKcompact hKu hu Z
        margin hmargin hlimitMargin M hM hlimitNorm eta heta
    filter_upwards [h] with a ha
    intro p hp j
    simpa [R, R0] using
      ha p.1 hp.1 (spectral p.2 j) (hspectral p.2 hp.2 j)
  have hpair :=
    finiteDimensional_realResolventNewtonHermitePair_tendsto_uniformOn_of_componentwise
      degree (fun _ => 0) 0 R R0 M hM hR0 hR
  intro epsilon hepsilon
  have h := hpair epsilon hepsilon
  filter_upwards [h] with a ha
  intro lambda hlambda q hq
  have ha' := ha (lambda, q) ⟨hlambda, hq⟩
  change
    ‖continuousLinearMapRealResolventNewtonHermitePairObservable degree
        (nodes q) (eval q) (R a (lambda, q)) -
      continuousLinearMapRealResolventNewtonHermitePairObservable degree
        (nodes q) (eval q) (R0 (lambda, q))‖ < epsilon
  simpa [R, R0, spectral,
    continuousLinearMapRealResolventNewtonHermitePairObservable_eq] using ha'

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D
