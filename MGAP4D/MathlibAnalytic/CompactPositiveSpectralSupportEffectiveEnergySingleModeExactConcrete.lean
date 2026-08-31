import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportEffectiveEnergyLimitConcrete
import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorResolventTuranEqualityGeneratorEigenmode
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End Filter
open scoped InnerProductSpace LinearPMap Topology BigOperators

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

universe u

/-- On a genuine actual-domain eigenmode of a coercive partially defined
operator, every factorial-normalized resolvent derivative ratio reconstructs
exactly the same generator energy. -/
theorem realLinearPMapAmbientResolventQuadraticAmplitude_effectiveEnergy_eq_domain_eigenvalue
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : E →ₗ.[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun)
    (u : E) (hu : u ≠ 0) (rho : ℝ) (x : A.domain)
    (hxu : (x : E) = u) (hAx : A x = rho • u)
    (n : ℕ) (lambda : ℝ) (hlambda : |lambda| < c) :
    let q := realLinearPMapAmbientResolventQuadraticAmplitude
      A c hc hNorm hKer hSurj u
    lambda +
        (iteratedDeriv (n + 1) q lambda /
          ((n + 1 : ℝ) * iteratedDeriv n q lambda))⁻¹ = rho := by
  dsimp only
  let q := realLinearPMapAmbientResolventQuadraticAmplitude
    A c hc hNorm hKer hSurj u
  let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
    A c hc hNorm hKer hSurj lambda
  rcases realLinearPMapAmbientResolventFamily_domain_eigenmode_to_eigenmode
      A c hc hNorm hKer hSurj lambda hlambda u hu rho x hxu hAx with
    ⟨hrholambda, hFu⟩
  let r : ℝ := (rho - lambda)⁻¹
  have hr : r ≠ 0 := by
    exact inv_ne_zero (sub_ne_zero.mpr hrholambda)
  have hFu' : F u = r • u := by
    simpa [F, r] using hFu
  have hpow : ∀ k : ℕ, (F ^ k) u = (r ^ k) • u := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ]
        change (F ^ k) (F u) = (r ^ (k + 1)) • u
        rw [hFu', map_smul, ih]
        simp [smul_smul, pow_succ, mul_comm]
  have huNorm : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have huInner : inner ℝ u u ≠ 0 := by
    rw [real_inner_self_eq_norm_sq]
    exact pow_ne_zero 2 huNorm
  have hinner : ∀ k : ℕ,
      inner ℝ ((F ^ k) u) u = r ^ k * inner ℝ u u := by
    intro k
    rw [hpow k, real_inner_smul_left]
  have hratio :
      iteratedDeriv (n + 1) q lambda /
          ((n + 1 : ℝ) * iteratedDeriv n q lambda) = r := by
    rw [realLinearPMapAmbientResolventQuadraticAmplitude_iteratedDeriv_eq_factorial
        A c hc hNorm hKer hSurj u n lambda hlambda,
      realLinearPMapAmbientResolventQuadraticAmplitude_iteratedDeriv_eq_factorial
        A c hc hNorm hKer hSurj u (n + 1) lambda hlambda]
    change
      (((n + 1).factorial : ℝ) * inner ℝ ((F ^ (n + 2)) u) u) /
          ((n + 1 : ℝ) *
            ((n.factorial : ℝ) * inner ℝ ((F ^ (n + 1)) u) u)) = r
    rw [hinner (n + 2), hinner (n + 1)]
    have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
    have hfac : (n.factorial : ℝ) ≠ 0 := by positivity
    have hrpow : r ^ (n + 1) ≠ 0 := pow_ne_zero _ hr
    norm_num [Nat.factorial_succ]
    field_simp [hn1, hfac, hrpow, huInner, hr]
    ring
  rw [hratio]
  simp [r]

/-- Native zero-eigenspace-support bridge for exact pure-mode effective-energy
reconstruction. Fixing the support carrier before invoking the generic theorem
avoids subtype inner-product instance diamonds in the physical specialization. -/
private theorem realHilbertZeroEigenspaceSupport_resolventQuadraticAmplitude_effectiveEnergy_eq_domain_eigenvalue
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) [CompleteSpace (realHilbertZeroEigenspaceSupport T)]
    (A : realHilbertZeroEigenspaceSupport T →ₗ.[ℝ] realHilbertZeroEigenspaceSupport T)
    (c : ℝ) (hc : 0 < c)
    (hNorm : ∀ x : A.domain,
      c * ‖(x : realHilbertZeroEigenspaceSupport T)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun)
    (u : realHilbertZeroEigenspaceSupport T) (hu : u ≠ 0)
    (rho : ℝ) (x : A.domain)
    (hxu : (x : realHilbertZeroEigenspaceSupport T) = u)
    (hAx : A x = rho • u)
    (n : ℕ) (lambda : ℝ) (hlambda : |lambda| < c) :
    let q := realLinearPMapAmbientResolventQuadraticAmplitude
      A c hc hNorm hKer hSurj u
    lambda +
        (iteratedDeriv (n + 1) q lambda /
          ((n + 1 : ℝ) * iteratedDeriv n q lambda))⁻¹ = rho := by
  exact
    realLinearPMapAmbientResolventQuadraticAmplitude_effectiveEnergy_eq_domain_eigenvalue
      A c hc hNorm hKer hSurj u hu rho x hxu hAx n lambda hlambda

local instance supportEffectiveEnergySingleModeExactConcreteSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance supportEffectiveEnergySingleModeExactConcreteSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance supportEffectiveEnergySingleModeExactConcreteSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance supportEffectiveEnergySingleModeExactConcreteSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance supportEffectiveEnergySingleModeExactConcreteSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance supportEffectiveEnergySingleModeExactConcreteSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance supportEffectiveEnergySingleModeExactConcreteSpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance supportEffectiveEnergySingleModeExactConcretePairHilbertSectorComplete
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    H N hN beta hbeta

/-- A physical state on the single-log-generator-mode locus carries one genuine
generator energy `rho` which is reconstructed exactly by every derivative order
at every admissible resolvent parameter. The asymptotic effective-energy limit
is the same `rho` simultaneously for the whole coercive gap. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_singleLogGeneratorMode_exactEffectiveEnergy
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta) (hv : v ≠ 0)
    (hmode :
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportIsSingleLogGeneratorMode
        H N hN beta hbeta v) :
    ∃ rho : ℝ, ∀ lambda : ℝ,
      |lambda| <
          2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
            H N hN beta hbeta →
        let q :=
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
            H N hN beta hbeta v
        (∀ n : ℕ,
          lambda +
              (iteratedDeriv (n + 1) q lambda /
                ((n + 1 : ℝ) * iteratedDeriv n q lambda))⁻¹ = rho) ∧
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_effectiveEnergyLimit
          H N hN beta hbeta v lambda = rho := by
  let T :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
      H N hN beta hbeta 1
  letI : CompleteSpace (realHilbertZeroEigenspaceSupport T) := by
    exact (realHilbertZeroEigenspaceSupport_isClosed T).completeSpace_coe
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
  change ∃ rho : ℝ, ∃ x : A.domain,
    (x : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta) = v ∧ A x = rho • v at hmode
  rcases hmode with ⟨rho, x, hxu, hAx⟩
  refine ⟨rho, ?_⟩
  intro lambda hlambda
  dsimp only
  let q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
      H N hN beta hbeta v
  have hlambda' : |lambda| < c := by
    simpa [c] using hlambda
  have hfinite : ∀ n : ℕ,
      lambda +
          (iteratedDeriv (n + 1) q lambda /
            ((n + 1 : ℝ) * iteratedDeriv n q lambda))⁻¹ = rho := by
    intro n
    have h :=
      realHilbertZeroEigenspaceSupport_resolventQuadraticAmplitude_effectiveEnergy_eq_domain_eigenvalue
        T A c hc hNorm hKer hSurj v hv rho x hxu hAx n lambda hlambda'
    simpa [
      q,
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude,
      A, c] using h
  let energy := fun n : ℕ =>
    lambda +
      (iteratedDeriv (n + 1) q lambda /
        ((n + 1 : ℝ) * iteratedDeriv n q lambda))⁻¹
  have ht :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_tendsto_effectiveEnergyLimit
      H N hN beta hbeta v hv lambda hlambda
  dsimp only at ht
  have ht' :
      Tendsto energy atTop
        (𝓝 (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_effectiveEnergyLimit
          H N hN beta hbeta v lambda)) := by
    simpa [energy, q] using ht
  have hconst : Tendsto energy atTop (𝓝 rho) := by
    have hfun : energy = fun _ : ℕ => rho := by
      funext n
      exact hfinite n
    rw [hfun]
    exact tendsto_const_nhds
  have hlimit :
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_effectiveEnergyLimit
        H N hN beta hbeta v lambda = rho :=
    tendsto_nhds_unique ht' hconst
  exact ⟨hfinite, hlimit⟩

/-- On the single-log-generator-mode locus, the asymptotic effective energy is
independent of the resolvent parameter throughout the full coercive gap. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_effectiveEnergyLimit_parameter_independent_of_logGeneratorMode
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta) (hv : v ≠ 0)
    (hmode :
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportIsSingleLogGeneratorMode
        H N hN beta hbeta v)
    (lambda mu : ℝ)
    (hlambda :
      |lambda| <
        2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta)
    (hmu :
      |mu| <
        2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_effectiveEnergyLimit
        H N hN beta hbeta v lambda =
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_effectiveEnergyLimit
        H N hN beta hbeta v mu := by
  rcases
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_singleLogGeneratorMode_exactEffectiveEnergy
        H N hN beta hbeta v hv hmode with
    ⟨rho, hall⟩
  have hl := hall lambda hlambda
  have hm := hall mu hmu
  dsimp only at hl hm
  rw [hl.2, hm.2]

end

end MathlibAnalytic
end MGAP4D
