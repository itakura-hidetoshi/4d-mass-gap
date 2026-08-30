import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorResolventTuranHierarchyConcrete
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End Filter
open scoped InnerProductSpace LinearPMap Topology BigOperators

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

universe u

/-- Shifted quadratic coercivity pulled back through the bounded ambient
resolvent.  Unlike the elementary operator-norm estimate, the sharp margin is
`c - lambda`, not `c - |lambda|`. -/
theorem realLinearPMapAmbientResolventFamily_gap_sub_mul_norm_sq_le_inner
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : E →ₗ.[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun)
    (hQuad : ∀ x : A.domain, c * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E))
    (lambda : ℝ) (hlambda : |lambda| < c) (y : E) :
    (c - lambda) *
        ‖realLinearPMapAmbientResolventFamily_of_norm_lower_bound
          A c hc hNorm hKer hSurj lambda y‖ ^ 2 ≤
      inner ℝ
        (realLinearPMapAmbientResolventFamily_of_norm_lower_bound
          A c hc hNorm hKer hSurj lambda y) y := by
  let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
    A c hc hNorm hKer hSurj
  rcases realLinearPMapAmbientResolventFamily_exists_domain_preimage
      A c hc hNorm hKer hSurj lambda hlambda y with
    ⟨x, hxy, hFx⟩
  have hq := hQuad x
  change (c - lambda) * ‖F lambda y‖ ^ 2 ≤ inner ℝ (F lambda y) y
  rw [hFx, ← hxy, real_inner_comm]
  change (c - lambda) * ‖(x : E)‖ ^ 2 ≤
    inner ℝ (A x - lambda • (x : E)) (x : E)
  rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  linarith

/-- The same pulled-back coercivity gives the sharp quadratic upper bound for
the ambient resolvent. -/
theorem realLinearPMapAmbientResolventFamily_inner_le_gap_sub_inv_mul_norm_sq
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : E →ₗ.[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun)
    (hQuad : ∀ x : A.domain, c * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E))
    (lambda : ℝ) (hlambda : |lambda| < c) (y : E) :
    inner ℝ
        (realLinearPMapAmbientResolventFamily_of_norm_lower_bound
          A c hc hNorm hKer hSurj lambda y) y ≤
      (c - lambda)⁻¹ * ‖y‖ ^ 2 := by
  let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
    A c hc hNorm hKer hSurj
  have hgap : 0 < c - lambda := by
    have hlt : lambda < c := lt_of_le_of_lt (le_abs_self lambda) hlambda
    linarith
  by_cases hy : y = 0
  · simp [hy]
  have hFy : F lambda y ≠ 0 := by
    intro hzero
    apply hy
    exact (realLinearPMapAmbientResolventFamily_eq_zero_iff
      A c hc hNorm hKer hSurj lambda hlambda y).mp hzero
  have hFnorm : 0 < ‖F lambda y‖ := norm_pos_iff.mpr hFy
  have hcoerc := realLinearPMapAmbientResolventFamily_gap_sub_mul_norm_sq_le_inner
    A c hc hNorm hKer hSurj hQuad lambda hlambda y
  have hcsabs := abs_real_inner_le_norm (F lambda y) y
  have hcs : inner ℝ (F lambda y) y ≤ ‖F lambda y‖ * ‖y‖ := by
    exact le_trans (le_abs_self _) hcsabs
  have hnormLinear : (c - lambda) * ‖F lambda y‖ ≤ ‖y‖ := by
    nlinarith
  have hscaled :
      (c - lambda) * inner ℝ (F lambda y) y ≤ ‖y‖ ^ 2 := by
    have hyNorm : 0 ≤ ‖y‖ := norm_nonneg y
    have hmul := mul_le_mul_of_nonneg_right hnormLinear hyNorm
    nlinarith
  have hscaled' :
      inner ℝ (F lambda y) y * (c - lambda) ≤ ‖y‖ ^ 2 := by
    simpa [mul_comm] using hscaled
  have hdiv : inner ℝ (F lambda y) y ≤ ‖y‖ ^ 2 / (c - lambda) := by
    exact (le_div_iff₀ hgap).2 hscaled'
  simpa [div_eq_mul_inv, mul_comm] using hdiv

/-- A self-adjoint bounded operator whose first two adjacent moment inequalities
have the same constant satisfies that inequality at every power.  The proof is
the parity-free two-step moment recursion. -/
theorem realContinuousLinearMap_pow_inner_succ_le_of_base_bounds
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (F : E →L[ℝ] E) (hSelf : IsSelfAdjoint F) (M : ℝ)
    (h0 : ∀ z : E, inner ℝ (F z) z ≤ M * ‖z‖ ^ 2)
    (h1 : ∀ z : E, ‖F z‖ ^ 2 ≤ M * inner ℝ (F z) z)
    (n : ℕ) (u : E) :
    inner ℝ ((F ^ (n + 1)) u) u ≤ M * inner ℝ ((F ^ n) u) u := by
  induction n using Nat.strong_induction_on generalizing u with
  | h n ih =>
      rcases n with _ | n
      · simpa [real_inner_self_eq_norm_sq] using h0 u
      · rcases n with _ | k
        · have hs := realContinuousLinearMap_pow_inner_shift_two F hSelf 0 u
          simp at hs
          change inner ℝ (F (F u)) u ≤ M * inner ℝ (F u) u
          rw [hs]
          exact h1 u
        · have hind := ih k (by omega) (F u)
          have hs0 := realContinuousLinearMap_pow_inner_shift_two F hSelf k u
          have hs1 := realContinuousLinearMap_pow_inner_shift_two F hSelf (k + 1) u
          rw [show k + 2 + 1 = (k + 1) + 2 by omega, hs1,
            show k + 2 = k + 2 by rfl, hs0]
          exact hind

/-- Every adjacent moment ratio of the coercive ambient resolvent is bounded by
the sharp inverse distance `1 / (c - lambda)`. -/
theorem realLinearPMapAmbientResolventFamily_pow_inner_succ_le_gap_sub_inv
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : E →ₗ.[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun)
    (hSelf : IsSelfAdjoint A)
    (hQuad : ∀ x : A.domain, c * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E))
    (lambda : ℝ) (hlambda : |lambda| < c) (n : ℕ) (u : E) :
    let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
      A c hc hNorm hKer hSurj lambda
    inner ℝ ((F ^ (n + 1)) u) u ≤
      (c - lambda)⁻¹ * inner ℝ ((F ^ n) u) u := by
  dsimp only
  let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
    A c hc hNorm hKer hSurj lambda
  have hgap : 0 < c - lambda := by
    have hlt : lambda < c := lt_of_le_of_lt (le_abs_self lambda) hlambda
    linarith
  have hFself := realLinearPMapAmbientResolventFamily_isSelfAdjoint_of_isSelfAdjoint
    A c hc hNorm hKer hSurj hSelf lambda hlambda
  have h0 : ∀ z : E, inner ℝ (F z) z ≤ (c - lambda)⁻¹ * ‖z‖ ^ 2 := by
    intro z
    simpa [F] using
      (realLinearPMapAmbientResolventFamily_inner_le_gap_sub_inv_mul_norm_sq
        A c hc hNorm hKer hSurj hQuad lambda hlambda z)
  have h1 : ∀ z : E, ‖F z‖ ^ 2 ≤ (c - lambda)⁻¹ * inner ℝ (F z) z := by
    intro z
    have hcoerc := realLinearPMapAmbientResolventFamily_gap_sub_mul_norm_sq_le_inner
      A c hc hNorm hKer hSurj hQuad lambda hlambda z
    have hcoerc' :
        ‖F z‖ ^ 2 * (c - lambda) ≤ inner ℝ (F z) z := by
      simpa [F, mul_comm] using hcoerc
    have hdiv : ‖F z‖ ^ 2 ≤ inner ℝ (F z) z / (c - lambda) := by
      exact (le_div_iff₀ hgap).2 hcoerc'
    simpa [div_eq_mul_inv, mul_comm] using hdiv
  exact realContinuousLinearMap_pow_inner_succ_le_of_base_bounds
    F hFself (c - lambda)⁻¹ h0 h1 n u

/-- Saturation-free sharp cap for every normalized derivative ratio of a
nonzero coercive resolvent quadratic amplitude. -/
theorem realLinearPMapAmbientResolventQuadraticAmplitude_derivativeRatio_le_gap_sub_inv
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : E →ₗ.[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun)
    (hSelf : IsSelfAdjoint A)
    (hQuad : ∀ x : A.domain, c * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E))
    (u : E) (hu : u ≠ 0) (n : ℕ) (lambda : ℝ) (hlambda : |lambda| < c) :
    let q := realLinearPMapAmbientResolventQuadraticAmplitude A c hc hNorm hKer hSurj u
    let R := iteratedDeriv (n + 1) q lambda /
      ((n + 1 : ℝ) * iteratedDeriv n q lambda)
    0 < R ∧ R ≤ (c - lambda)⁻¹ := by
  dsimp only
  let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
    A c hc hNorm hKer hSurj lambda
  let q := realLinearPMapAmbientResolventQuadraticAmplitude A c hc hNorm hKer hSurj u
  have hn := realLinearPMapAmbientResolventQuadraticAmplitude_iteratedDeriv_pos
    A c hc hNorm hKer hSurj hSelf hQuad u hu n lambda hlambda
  have hn1 := realLinearPMapAmbientResolventQuadraticAmplitude_iteratedDeriv_pos
    A c hc hNorm hKer hSurj hSelf hQuad u hu (n + 1) lambda hlambda
  have hRpos : 0 < iteratedDeriv (n + 1) q lambda /
      ((n + 1 : ℝ) * iteratedDeriv n q lambda) := by
    dsimp [q]
    positivity
  have hmoment := realLinearPMapAmbientResolventFamily_pow_inner_succ_le_gap_sub_inv
    A c hc hNorm hKer hSurj hSelf hQuad lambda hlambda (n + 1) u
  dsimp only at hmoment
  have hformulaN :=
    realLinearPMapAmbientResolventQuadraticAmplitude_iteratedDeriv_eq_factorial
      A c hc hNorm hKer hSurj u n lambda hlambda
  have hformulaN1 :=
    realLinearPMapAmbientResolventQuadraticAmplitude_iteratedDeriv_eq_factorial
      A c hc hNorm hKer hSurj u (n + 1) lambda hlambda
  have hnum :
      iteratedDeriv (n + 1) q lambda ≤
        (c - lambda)⁻¹ * ((n + 1 : ℝ) * iteratedDeriv n q lambda) := by
    rw [hformulaN, hformulaN1]
    change
      ((n + 1).factorial : ℝ) * inner ℝ ((F ^ (n + 2)) u) u ≤
        (c - lambda)⁻¹ *
          ((n + 1 : ℝ) * ((n.factorial : ℝ) * inner ℝ ((F ^ (n + 1)) u) u))
    have hscaled := mul_le_mul_of_nonneg_left hmoment
      (show 0 ≤ ((n + 1).factorial : ℝ) by positivity)
    norm_num [Nat.factorial_succ] at hscaled ⊢
    ring_nf at hscaled ⊢
    exact hscaled
  have hden : 0 < (n + 1 : ℝ) * iteratedDeriv n q lambda := by
    dsimp [q]
    positivity
  have hupper : iteratedDeriv (n + 1) q lambda /
      ((n + 1 : ℝ) * iteratedDeriv n q lambda) ≤ (c - lambda)⁻¹ := by
    exact (div_le_iff₀ hden).2 hnum
  exact ⟨hRpos, hupper⟩

/-- Native zero-eigenspace-support bridge for the saturation-free sharp cap.
Fixing the support carrier before invoking the generic theorem avoids subtype
inner-product instance diamonds in the concrete physical specialization. -/
private theorem realHilbertZeroEigenspaceSupport_resolventQuadraticAmplitude_derivativeRatio_le_gap_sub_inv
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) [CompleteSpace (realHilbertZeroEigenspaceSupport T)]
    (A : realHilbertZeroEigenspaceSupport T →ₗ.[ℝ] realHilbertZeroEigenspaceSupport T)
    (c : ℝ) (hc : 0 < c)
    (hNorm : ∀ x : A.domain,
      c * ‖(x : realHilbertZeroEigenspaceSupport T)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun)
    (hSelf : IsSelfAdjoint A)
    (hQuad : ∀ x : A.domain,
      c * ‖(x : realHilbertZeroEigenspaceSupport T)‖ ^ 2 ≤
        inner ℝ (A x) (x : realHilbertZeroEigenspaceSupport T))
    (v : realHilbertZeroEigenspaceSupport T) (hv : v ≠ 0)
    (n : ℕ) (lambda : ℝ) (hlambda : |lambda| < c) :
    let q := realLinearPMapAmbientResolventQuadraticAmplitude
      A c hc hNorm hKer hSurj v
    let R := iteratedDeriv (n + 1) q lambda /
      ((n + 1 : ℝ) * iteratedDeriv n q lambda)
    0 < R ∧ R ≤ (c - lambda)⁻¹ := by
  exact realLinearPMapAmbientResolventQuadraticAmplitude_derivativeRatio_le_gap_sub_inv
    A c hc hNorm hKer hSurj hSelf hQuad v hv n lambda hlambda

local instance sharpGapCapSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance sharpGapCapSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance sharpGapCapSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance sharpGapCapSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance sharpGapCapSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance sharpGapCapSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance sharpGapCapSpatialSliceHaarSFinite
    (H N : ℕ) : SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance sharpGapCapPairHilbertSectorComplete
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    H N hN beta hbeta

local instance sharpGapCapSpectralSupportComplete
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
  exact
    (realHilbertZeroEigenspaceSupport_isClosed
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
        H N hN beta hbeta 1)).completeSpace_coe

/-- For every nonzero physical support state, every derivative order, and every
resolvent parameter in the finite-volume coercive gap, the directly observable
normalized derivative ratio is positive and bounded by the sharp inverse gap
distance.  No Turán saturation hypothesis is required. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_le_gapResolventDistance
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta) (hv : v ≠ 0) (n : ℕ) (lambda : ℝ)
    (hlambda :
      |lambda| <
        2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta) :
    let q :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
        H N hN beta hbeta v
    let R := iteratedDeriv (n + 1) q lambda /
      ((n + 1 : ℝ) * iteratedDeriv n q lambda)
    let c :=
      2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
        H N hN beta hbeta
    0 < R ∧ R ≤ (c - lambda)⁻¹ := by
  dsimp only
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
    H N hN beta hbeta 1
  letI : CompleteSpace (realHilbertZeroEigenspaceSupport T) :=
    (realHilbertZeroEigenspaceSupport_isClosed T).completeSpace_coe
  let hCompact : IsCompactOperator T :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isCompact_of_pos
      H N hN beta hbeta 1 (by norm_num)
  let hPositive : T.IsPositive :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isPositive
      H N hN beta hbeta 1
  let A := periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
    H N hN beta hbeta
  let c := 2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
    H N hN beta hbeta
  have hc : 0 < c := by
    exact mul_pos (by norm_num)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate_pos
        H N hN beta hbeta)
  have hNorm : ∀ x : A.domain,
      c * ‖(x : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta)‖ ≤ ‖A x‖ := by
    intro x
    simpa [A, c] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_norm_lower_bound
        H N hN beta hbeta x)
  have hKer : ∀ x : A.domain, A x = 0 → x = 0 := by
    intro x hx
    exact periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_eq_zero_of_apply_eq_zero
      H N hN beta hbeta x hx
  have hSurj : Function.Surjective A.toFun := by
    simpa [A] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_surjective
        H N hN beta hbeta)
  have hQuad : ∀ x : A.domain,
      c * ‖(x : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta)‖ ^ 2 ≤
        inner ℝ (A x)
          (x : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
            H N hN beta hbeta) := by
    intro x
    simpa [A, c] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_quadratic_lower_bound
        H N hN beta hbeta x)
  have hGenerator : realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive = A := by
    dsimp only [T, A]
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
    rfl
  have hSelfNative := realHilbertCompactPositiveZeroSupportLogGenerator_isSelfAdjoint
    T hCompact hPositive
  rw [hGenerator] at hSelfNative
  have hcap :=
    realHilbertZeroEigenspaceSupport_resolventQuadraticAmplitude_derivativeRatio_le_gap_sub_inv
      T A c hc hNorm hKer hSurj hSelfNative hQuad v hv n lambda
        (by simpa [c] using hlambda)
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude,
    A, c] using hcap

end

end MathlibAnalytic
end MGAP4D
