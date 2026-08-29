import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorResolventQuadraticAbsoluteMonotonicity
import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorNormCoercive
import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorRangeSurjective
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End Filter
open scoped InnerProductSpace LinearPMap Topology BigOperators

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

universe u

/-- A positive quadratic lower bound for a partially defined real-Hilbert
operator implies the corresponding graph-norm lower bound. -/
theorem realLinearPMap_norm_lower_bound_of_quadratic_lower_bound
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hQuad : ∀ x : A.domain,
      c * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E)) :
    ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖ := by
  intro x
  exact
    realHilbert_norm_lower_bound_of_quadratic_lower_bound
      c hc.le (A x) (x : E) (hQuad x)

/-- Strict quadratic coercivity forces the actual-domain kernel to vanish. -/
theorem realLinearPMap_eq_zero_of_apply_eq_zero_of_quadratic_lower_bound
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hQuad : ∀ x : A.domain,
      c * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E)) :
    ∀ x : A.domain, A x = 0 → x = 0 := by
  intro x hx
  have hNorm :=
    realLinearPMap_norm_lower_bound_of_quadratic_lower_bound
      A c hc hQuad x
  rw [hx, norm_zero] at hNorm
  have hxnorm : ‖(x : E)‖ = 0 := by
    nlinarith [norm_nonneg (x : E)]
  apply Subtype.ext
  exact norm_eq_zero.mp hxnorm

/-- Self-adjointness plus a strictly positive quadratic lower bound gives full
actual range.  Closedness follows from graph closedness and coercivity, while
density follows from self-adjointness and the trivial kernel. -/
theorem realLinearPMap_surjective_of_isSelfAdjoint_of_quadratic_lower_bound
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hSelf : IsSelfAdjoint A)
    (hQuad : ∀ x : A.domain,
      c * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E)) :
    Function.Surjective A.toFun := by
  let hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖ :=
    realLinearPMap_norm_lower_bound_of_quadratic_lower_bound A c hc hQuad
  let hKer : ∀ x : A.domain, A x = 0 → x = 0 :=
    realLinearPMap_eq_zero_of_apply_eq_zero_of_quadratic_lower_bound
      A c hc hQuad
  have hClosed : IsClosed (LinearMap.range A.toFun : Set E) :=
    realLinearPMap_range_isClosed_of_isClosed_of_norm_lower_bound
      A c hc hSelf.isClosed hNorm
  have hDense : (LinearMap.range A.toFun).topologicalClosure = ⊤ :=
    realLinearPMap_range_topologicalClosure_eq_top_of_isSelfAdjoint
      A hSelf hKer
  have hTop : LinearMap.range A.toFun = ⊤ :=
    realLinearPMap_range_eq_top_of_isClosed_of_topologicalClosure_eq_top
      A hClosed hDense
  intro y
  have hy : y ∈ LinearMap.range A.toFun := by
    rw [hTop]
    trivial
  exact hy

/-- Canonical ambient resolvent generated solely from self-adjointness and a
strict quadratic lower bound.  The forward operator remains partially defined. -/
noncomputable def realLinearPMapAmbientResolventFamily_of_selfAdjoint_of_quadratic_lower_bound
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hSelf : IsSelfAdjoint A)
    (hQuad : ∀ x : A.domain,
      c * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E))
    (lambda : ℝ) : E →L[ℝ] E :=
  realLinearPMapAmbientResolventFamily_of_norm_lower_bound
    A c hc
    (realLinearPMap_norm_lower_bound_of_quadratic_lower_bound A c hc hQuad)
    (realLinearPMap_eq_zero_of_apply_eq_zero_of_quadratic_lower_bound A c hc hQuad)
    (realLinearPMap_surjective_of_isSelfAdjoint_of_quadratic_lower_bound
      A c hc hSelf hQuad)
    lambda

/-- Diagonal scalar amplitude of the canonical resolvent determined by
self-adjoint quadratic coercivity. -/
noncomputable def realLinearPMapAmbientResolventQuadraticAmplitude_of_selfAdjoint_of_quadratic_lower_bound
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hSelf : IsSelfAdjoint A)
    (hQuad : ∀ x : A.domain,
      c * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E))
    (u : E)
    (lambda : ℝ) : ℝ :=
  realLinearPMapAmbientResolventQuadraticAmplitude
    A c hc
    (realLinearPMap_norm_lower_bound_of_quadratic_lower_bound A c hc hQuad)
    (realLinearPMap_eq_zero_of_apply_eq_zero_of_quadratic_lower_bound A c hc hQuad)
    (realLinearPMap_surjective_of_isSelfAdjoint_of_quadratic_lower_bound
      A c hc hSelf hQuad)
    u lambda

/-- Every power of the coercively generated canonical resolvent has a
nonnegative quadratic form. -/
theorem realLinearPMapAmbientResolventFamily_pow_inner_nonneg_of_selfAdjoint_of_quadratic_lower_bound
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hSelf : IsSelfAdjoint A)
    (hQuad : ∀ x : A.domain,
      c * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E))
    (lambda : ℝ)
    (hlambda : |lambda| < c)
    (n : ℕ)
    (u : E) :
    0 ≤ inner ℝ
      ((realLinearPMapAmbientResolventFamily_of_selfAdjoint_of_quadratic_lower_bound
        A c hc hSelf hQuad lambda ^ n) u)
      u := by
  unfold realLinearPMapAmbientResolventFamily_of_selfAdjoint_of_quadratic_lower_bound
  exact
    realLinearPMapAmbientResolventFamily_pow_inner_nonneg
      A c hc
      (realLinearPMap_norm_lower_bound_of_quadratic_lower_bound A c hc hQuad)
      (realLinearPMap_eq_zero_of_apply_eq_zero_of_quadratic_lower_bound A c hc hQuad)
      (realLinearPMap_surjective_of_isSelfAdjoint_of_quadratic_lower_bound
        A c hc hSelf hQuad)
      hSelf hQuad lambda hlambda n u

/-- Exact all-order derivative formula for the coercively generated quadratic
resolvent amplitude. -/
theorem realLinearPMapAmbientResolventQuadraticAmplitude_iteratedDeriv_eq_factorial_of_selfAdjoint_of_quadratic_lower_bound
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hSelf : IsSelfAdjoint A)
    (hQuad : ∀ x : A.domain,
      c * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E))
    (u : E)
    (n : ℕ)
    (lambda : ℝ)
    (hlambda : |lambda| < c) :
    iteratedDeriv n
        (realLinearPMapAmbientResolventQuadraticAmplitude_of_selfAdjoint_of_quadratic_lower_bound
          A c hc hSelf hQuad u)
        lambda =
      (n.factorial : ℝ) * inner ℝ
        ((realLinearPMapAmbientResolventFamily_of_selfAdjoint_of_quadratic_lower_bound
          A c hc hSelf hQuad lambda ^ (n + 1)) u)
        u := by
  unfold realLinearPMapAmbientResolventQuadraticAmplitude_of_selfAdjoint_of_quadratic_lower_bound
  unfold realLinearPMapAmbientResolventFamily_of_selfAdjoint_of_quadratic_lower_bound
  exact
    realLinearPMapAmbientResolventQuadraticAmplitude_iteratedDeriv_eq_factorial
      A c hc
      (realLinearPMap_norm_lower_bound_of_quadratic_lower_bound A c hc hQuad)
      (realLinearPMap_eq_zero_of_apply_eq_zero_of_quadratic_lower_bound A c hc hQuad)
      (realLinearPMap_surjective_of_isSelfAdjoint_of_quadratic_lower_bound
        A c hc hSelf hQuad)
      u n lambda hlambda

/-- Absolute monotonicity now needs only the intrinsic operator hypotheses:
self-adjointness and a strictly positive quadratic lower bound. -/
theorem realLinearPMapAmbientResolventQuadraticAmplitude_iteratedDeriv_nonneg_of_selfAdjoint_of_quadratic_lower_bound
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hSelf : IsSelfAdjoint A)
    (hQuad : ∀ x : A.domain,
      c * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E))
    (u : E)
    (n : ℕ)
    (lambda : ℝ)
    (hlambda : |lambda| < c) :
    0 ≤ iteratedDeriv n
      (realLinearPMapAmbientResolventQuadraticAmplitude_of_selfAdjoint_of_quadratic_lower_bound
        A c hc hSelf hQuad u)
      lambda := by
  rw [realLinearPMapAmbientResolventQuadraticAmplitude_iteratedDeriv_eq_factorial_of_selfAdjoint_of_quadratic_lower_bound
    A c hc hSelf hQuad u n lambda hlambda]
  exact mul_nonneg (by positivity)
    (realLinearPMapAmbientResolventFamily_pow_inner_nonneg_of_selfAdjoint_of_quadratic_lower_bound
      A c hc hSelf hQuad lambda hlambda (n + 1) u)

local instance supportResolventConcreteSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance supportResolventConcreteSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance supportResolventConcreteSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance supportResolventConcreteSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance supportResolventConcreteSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance supportResolventConcreteSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance supportResolventConcreteSpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance supportResolventConcretePairHilbertSectorComplete
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    H N hN beta hbeta

/-- Quadratic coercivity for the actual support logarithmic Hamiltonian written
on the canonical zero-eigenspace-support Hilbert carrier rather than through
the long physical carrier alias. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneNativeSupportLogGenerator_quadratic_lower_bound
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    let T :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
        H N hN beta hbeta 1
    let hCompact : IsCompactOperator T :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isCompact_of_pos
        H N hN beta hbeta 1 (by norm_num)
    let hPositive : T.IsPositive :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isPositive
        H N hN beta hbeta 1
    let A := realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive
    let c :=
      2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
        H N hN beta hbeta
    ∀ x : A.domain,
      c * ‖(x : realHilbertZeroEigenspaceSupport T)‖ ^ 2 ≤
        inner ℝ (A x) (x : realHilbertZeroEigenspaceSupport T) := by
  dsimp only
  intro x
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator,
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport]
    using
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_quadratic_lower_bound
        H N hN beta hbeta x)

/-- Physical specialization: every derivative of every diagonal matrix element
of the actual one-step support logarithmic resolvent is nonnegative throughout
`|λ| < 2r`, expressed on the canonical positive spectral-support carrier. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneNativeSupportResolventQuadratic_iteratedDeriv_nonneg
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    let T :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
        H N hN beta hbeta 1
    let hCompact : IsCompactOperator T :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isCompact_of_pos
        H N hN beta hbeta 1 (by norm_num)
    let hPositive : T.IsPositive :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isPositive
        H N hN beta hbeta 1
    let A := realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive
    let c :=
      2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
        H N hN beta hbeta
    let hc : 0 < c := by
      exact mul_pos (by norm_num)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate_pos
          H N hN beta hbeta)
    let hSelf : IsSelfAdjoint A :=
      realHilbertCompactPositiveZeroSupportLogGenerator_isSelfAdjoint
        T hCompact hPositive
    let hQuad : ∀ x : A.domain,
        c * ‖(x : realHilbertZeroEigenspaceSupport T)‖ ^ 2 ≤
          inner ℝ (A x) (x : realHilbertZeroEigenspaceSupport T) :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneNativeSupportLogGenerator_quadratic_lower_bound
        H N hN beta hbeta
    ∀ (u : realHilbertZeroEigenspaceSupport T) (n : ℕ) (lambda : ℝ),
      |lambda| < c →
        0 ≤ iteratedDeriv n
          (realLinearPMapAmbientResolventQuadraticAmplitude_of_selfAdjoint_of_quadratic_lower_bound
            A c hc hSelf hQuad u)
          lambda := by
  dsimp only
  intro u n lambda hlambda
  exact
    realLinearPMapAmbientResolventQuadraticAmplitude_iteratedDeriv_nonneg_of_selfAdjoint_of_quadratic_lower_bound
      _ _ _ _ _ u n lambda hlambda

end

end MathlibAnalytic
end MGAP4D
