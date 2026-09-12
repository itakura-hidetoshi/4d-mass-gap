import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportTransferGeneratorExactSpectralDictionaryConcrete
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End Filter
open scoped InnerProductSpace LinearPMap Topology BigOperators

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

universe u

/-- On a genuine actual-domain generator eigenmode, every factorial-normalized
consecutive derivative ratio of the ambient resolvent quadratic amplitude is
exactly the bounded-resolvent eigenvalue `(rho - lambda)⁻¹`. -/
theorem realLinearPMapAmbientResolventQuadraticAmplitude_derivativeRatio_eq_of_domain_eigenmode
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : E →ₗ.[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun)
    (hSelf : IsSelfAdjoint A)
    (hQuad : ∀ x : A.domain,
      c * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E))
    (u : E) (hu : u ≠ 0) (rho : ℝ) (x : A.domain)
    (hxu : (x : E) = u) (hAx : A x = rho • u)
    (n : ℕ) (lambda : ℝ) (hlambda : |lambda| < c) :
    let q := realLinearPMapAmbientResolventQuadraticAmplitude
      A c hc hNorm hKer hSurj u
    iteratedDeriv (n + 1) q lambda /
        ((n + 1 : ℝ) * iteratedDeriv n q lambda) =
      (rho - lambda)⁻¹ := by
  dsimp only
  let q := realLinearPMapAmbientResolventQuadraticAmplitude
    A c hc hNorm hKer hSurj u
  let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
    A c hc hNorm hKer hSurj lambda
  let r : ℝ := (rho - lambda)⁻¹
  rcases
    realLinearPMapAmbientResolventFamily_domain_eigenmode_to_eigenmode
      A c hc hNorm hKer hSurj lambda hlambda u hu rho x hxu hAx with
    ⟨hrholambda, hFuRaw⟩
  have hFu : F u = r • u := by
    simpa [F, r] using hFuRaw
  have hpowShift : (F ^ (n + 2)) u = r • (F ^ (n + 1)) u := by
    have hp : F ^ (n + 2) = F ^ (n + 1) * F := by
      simpa [Nat.add_assoc] using pow_succ F (n + 1)
    rw [hp]
    change (F ^ (n + 1)) (F u) = r • (F ^ (n + 1)) u
    rw [hFu, map_smul]
  have hmoment :
      inner ℝ ((F ^ (n + 2)) u) u =
        r * inner ℝ ((F ^ (n + 1)) u) u := by
    rw [hpowShift, real_inner_smul_left]
  have hn : 0 < iteratedDeriv n q lambda := by
    simpa [q] using
      (realLinearPMapAmbientResolventQuadraticAmplitude_iteratedDeriv_pos
        A c hc hNorm hKer hSurj hSelf hQuad u hu n lambda hlambda)
  have hden :
      (n + 1 : ℝ) * iteratedDeriv n q lambda ≠ 0 :=
    ne_of_gt (mul_pos (by positivity) hn)
  apply (div_eq_iff hden).2
  rw [realLinearPMapAmbientResolventQuadraticAmplitude_iteratedDeriv_eq_factorial
      A c hc hNorm hKer hSurj u (n + 1) lambda hlambda,
    realLinearPMapAmbientResolventQuadraticAmplitude_iteratedDeriv_eq_factorial
      A c hc hNorm hKer hSurj u n lambda hlambda]
  change
    (((n + 1).factorial : ℝ) * inner ℝ ((F ^ (n + 2)) u) u) =
      r * ((n + 1 : ℝ) *
        ((n.factorial : ℝ) * inner ℝ ((F ^ (n + 1)) u) u))
  rw [hmoment]
  norm_num [Nat.factorial_succ]
  ring

/-- A single normalized derivative ratio reconstructs the generator energy on
a genuine spectral mode.  The ratio is nonzero and obeys the exact reciprocal
shift formula `rho = lambda + R_n(lambda)⁻¹`. -/
theorem realLinearPMapAmbientResolventQuadraticAmplitude_recover_domain_eigenvalue_from_derivativeRatio
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : E →ₗ.[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun)
    (hSelf : IsSelfAdjoint A)
    (hQuad : ∀ x : A.domain,
      c * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E))
    (u : E) (hu : u ≠ 0) (rho : ℝ) (x : A.domain)
    (hxu : (x : E) = u) (hAx : A x = rho • u)
    (n : ℕ) (lambda : ℝ) (hlambda : |lambda| < c) :
    let q := realLinearPMapAmbientResolventQuadraticAmplitude
      A c hc hNorm hKer hSurj u
    let R := iteratedDeriv (n + 1) q lambda /
      ((n + 1 : ℝ) * iteratedDeriv n q lambda)
    R ≠ 0 ∧ rho = lambda + R⁻¹ := by
  dsimp only
  let q := realLinearPMapAmbientResolventQuadraticAmplitude
    A c hc hNorm hKer hSurj u
  let R := iteratedDeriv (n + 1) q lambda /
    ((n + 1 : ℝ) * iteratedDeriv n q lambda)
  change R ≠ 0 ∧ rho = lambda + R⁻¹
  have hR : R = (rho - lambda)⁻¹ := by
    simpa [R, q] using
      (realLinearPMapAmbientResolventQuadraticAmplitude_derivativeRatio_eq_of_domain_eigenmode
        A c hc hNorm hKer hSurj hSelf hQuad u hu rho x hxu hAx n lambda hlambda)
  have hrholambda : rho ≠ lambda :=
    (realLinearPMapAmbientResolventFamily_domain_eigenmode_to_eigenmode
      A c hc hNorm hKer hSurj lambda hlambda u hu rho x hxu hAx).1
  have hdiff : rho - lambda ≠ 0 := sub_ne_zero.mpr hrholambda
  refine ⟨?_, ?_⟩
  · rw [hR]
    exact inv_ne_zero hdiff
  · rw [hR]
    simp

/-- Native zero-eigenspace-support bridge for the exact derivative-ratio formula.
Keeping the support as `realHilbertZeroEigenspaceSupport T` fixes its Hilbert
instances before the partially defined generator enters adjoint search. -/
private theorem realHilbertZeroEigenspaceSupport_resolventQuadraticAmplitude_derivativeRatio_eq_of_domain_eigenmode
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
    (u : realHilbertZeroEigenspaceSupport T) (hu : u ≠ 0)
    (rho : ℝ) (x : A.domain)
    (hxu : (x : realHilbertZeroEigenspaceSupport T) = u)
    (hAx : A x = rho • u)
    (n : ℕ) (lambda : ℝ) (hlambda : |lambda| < c) :
    let q := realLinearPMapAmbientResolventQuadraticAmplitude
      A c hc hNorm hKer hSurj u
    iteratedDeriv (n + 1) q lambda /
        ((n + 1 : ℝ) * iteratedDeriv n q lambda) =
      (rho - lambda)⁻¹ := by
  exact
    realLinearPMapAmbientResolventQuadraticAmplitude_derivativeRatio_eq_of_domain_eigenmode
      A c hc hNorm hKer hSurj hSelf hQuad u hu rho x hxu hAx n lambda hlambda

local instance exactDerivativeRatioConcreteSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance exactDerivativeRatioConcreteSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance exactDerivativeRatioConcreteSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance exactDerivativeRatioConcreteSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance exactDerivativeRatioConcreteSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance exactDerivativeRatioConcreteSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance exactDerivativeRatioConcreteSpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance exactDerivativeRatioConcretePairHilbertSectorComplete
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    H N hN beta hbeta

/-- Concrete physical specialization of the exact pure-mode derivative-ratio
formula. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_eq_of_logGeneratorEigenmode
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta) (hv : v ≠ 0)
    (rho : ℝ)
    (x : (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
      H N hN beta hbeta).domain)
    (hxv :
      (x : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta) = v)
    (hAx :
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
        H N hN beta hbeta x = rho • v)
    (n : ℕ) (lambda : ℝ)
    (hlambda :
      |lambda| <
        2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta) :
    let q :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
        H N hN beta hbeta v
    iteratedDeriv (n + 1) q lambda /
        ((n + 1 : ℝ) * iteratedDeriv n q lambda) =
      (rho - lambda)⁻¹ := by
  dsimp only
  let T :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
      H N hN beta hbeta 1
  letI : CompleteSpace (realHilbertZeroEigenspaceSupport T) := by
    exact (realHilbertZeroEigenspaceSupport_isClosed T).completeSpace_coe
  let hCompact : IsCompactOperator T :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isCompact_of_pos
      H N hN beta hbeta 1 (by norm_num)
  let hPositive : T.IsPositive :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isPositive
      H N hN beta hbeta 1
  let A :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
      H N hN beta hbeta
  let c :=
    2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
      H N hN beta hbeta
  have hc : 0 < c := by
    exact mul_pos (by norm_num)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate_pos
        H N hN beta hbeta)
  have hNorm : ∀ y : A.domain,
      c * ‖(y : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta)‖ ≤ ‖A y‖ := by
    intro y
    simpa [A, c] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_norm_lower_bound
        H N hN beta hbeta y)
  have hKer : ∀ y : A.domain, A y = 0 → y = 0 := by
    intro y hy
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_eq_zero_of_apply_eq_zero
        H N hN beta hbeta y hy
  have hSurj : Function.Surjective A.toFun := by
    simpa [A] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_surjective
        H N hN beta hbeta)
  have hQuad : ∀ y : A.domain,
      c * ‖(y : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta)‖ ^ 2 ≤
        inner ℝ (A y)
          (y : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
            H N hN beta hbeta) := by
    intro y
    simpa [A, c] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_quadratic_lower_bound
        H N hN beta hbeta y)
  have hGenerator :
      realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive = A := by
    dsimp only [T, A]
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
    rfl
  have hSelfNative :=
    realHilbertCompactPositiveZeroSupportLogGenerator_isSelfAdjoint
      T hCompact hPositive
  rw [hGenerator] at hSelfNative
  have h :=
    realHilbertZeroEigenspaceSupport_resolventQuadraticAmplitude_derivativeRatio_eq_of_domain_eigenmode
      T A c hc hNorm hKer hSurj hSelfNative hQuad v hv rho x hxv hAx n lambda
      (by simpa [c] using hlambda)
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude,
    A, c] using h

/-- On the exact physical transfer/generator spectral-pair locus, a normalized
derivative ratio reconstructs both the unique logarithmic energy and the unique
positive transfer eigenvalue. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport_exactSpectralPair_reconstructed_by_derivativeRatio
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta) (hv : v ≠ 0)
    (hpair :
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportHasUniqueTransferGeneratorSpectralPair
        H N hN beta hbeta v)
    (n : ℕ) (lambda : ℝ)
    (hlambda :
      |lambda| <
        2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta) :
    let q :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
        H N hN beta hbeta v
    let R := iteratedDeriv (n + 1) q lambda /
      ((n + 1 : ℝ) * iteratedDeriv n q lambda)
    ∃ tau rho : ℝ,
      0 < tau ∧
      tau = Real.exp (-rho) ∧
      rho = -Real.log tau ∧
      R = (rho - lambda)⁻¹ ∧
      R ≠ 0 ∧
      rho = lambda + R⁻¹ ∧
      tau = Real.exp (-(lambda + R⁻¹)) := by
  dsimp only
  let E :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta
  let T : E →L[ℝ] E :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
      H N hN beta hbeta 1
  let A :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
      H N hN beta hbeta
  let q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
      H N hN beta hbeta v
  let R := iteratedDeriv (n + 1) q lambda /
    ((n + 1 : ℝ) * iteratedDeriv n q lambda)
  change
    (∃! tau : ℝ,
      ∃! rho : ℝ,
        0 < tau ∧
        tau = Real.exp (-rho) ∧
        rho = -Real.log tau ∧
        T (v : E) = tau • (v : E) ∧
        ∃ x : A.domain,
          (x : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
            H N hN beta hbeta) = v ∧
          A x = rho • v) at hpair
  rcases hpair with ⟨tau, htauPair, _⟩
  rcases htauPair with ⟨rho, hrho, _⟩
  rcases hrho with ⟨htau, htaurho, hrhotau, _, x, hxv, hAx⟩
  have hR : R = (rho - lambda)⁻¹ := by
    simpa [R, q, A] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_eq_of_logGeneratorEigenmode
        H N hN beta hbeta v hv rho x hxv hAx n lambda hlambda)
  have hrholambda : rho ≠ lambda := by
    intro heq
    have hzero : (rho - lambda)⁻¹ = 0 := by simp [heq]
    have hpos : 0 < R := by
      have hn :=
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_iteratedDeriv_pos
          H N hN beta hbeta v hv n lambda hlambda
      have hn1 :=
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_iteratedDeriv_pos
          H N hN beta hbeta v hv (n + 1) lambda hlambda
      dsimp [R]
      positivity
    rw [hR, hzero] at hpos
    exact (lt_irrefl 0) hpos
  have hR0 : R ≠ 0 := by
    rw [hR]
    exact inv_ne_zero (sub_ne_zero.mpr hrholambda)
  have hreconstruct : rho = lambda + R⁻¹ := by
    rw [hR]
    simp
  refine ⟨tau, rho, htau, htaurho, hrhotau, hR, hR0, hreconstruct, ?_⟩
  calc
    tau = Real.exp (-rho) := htaurho
    _ = Real.exp (-(lambda + R⁻¹)) := by rw [hreconstruct]

end

end MathlibAnalytic
end MGAP4D