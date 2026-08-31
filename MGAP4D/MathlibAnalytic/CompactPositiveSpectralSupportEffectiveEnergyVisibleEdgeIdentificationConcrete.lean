import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorResolventVisibleEffectiveEnergy
import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportEffectiveEnergyLimitConcrete
import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportVisibleLogEnergyEdgeConcrete
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End Filter
open scoped InnerProductSpace lp LinearPMap Topology BigOperators

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

universe u

/-- The factorial-normalized derivative effective energy is exactly the
reciprocal adjacent resolvent-moment ratio. -/
theorem realLinearPMapAmbientResolventQuadraticAmplitude_effectiveEnergy_eq_powInnerRatio
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : E →ₗ.[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun) (hSelf : IsSelfAdjoint A)
    (hQuad : ∀ x : A.domain, c * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E))
    (u : E) (hu : u ≠ 0) (n : ℕ) (lambda : ℝ) (hlambda : |lambda| < c) :
    let q := realLinearPMapAmbientResolventQuadraticAmplitude A c hc hNorm hKer hSurj u
    let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound A c hc hNorm hKer hSurj lambda
    lambda + (iteratedDeriv (n + 1) q lambda / ((n + 1 : ℝ) * iteratedDeriv n q lambda))⁻¹ =
      lambda + inner ℝ ((F ^ (n + 1)) u) u / inner ℝ ((F ^ (n + 2)) u) u := by
  dsimp only
  let q := realLinearPMapAmbientResolventQuadraticAmplitude A c hc hNorm hKer hSurj u
  let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound A c hc hNorm hKer hSurj lambda
  have hposN1 := realLinearPMapAmbientResolventQuadraticAmplitude_iteratedDeriv_pos
    A c hc hNorm hKer hSurj hSelf hQuad u hu (n + 1) lambda hlambda
  have hformulaN := realLinearPMapAmbientResolventQuadraticAmplitude_iteratedDeriv_eq_factorial
    A c hc hNorm hKer hSurj u n lambda hlambda
  have hformulaN1 := realLinearPMapAmbientResolventQuadraticAmplitude_iteratedDeriv_eq_factorial
    A c hc hNorm hKer hSurj u (n + 1) lambda hlambda
  have hmN1 : inner ℝ ((F ^ (n + 2)) u) u ≠ 0 := by
    intro hm
    rw [hformulaN1] at hposN1
    change 0 < ((n + 1).factorial : ℝ) * inner ℝ ((F ^ (n + 2)) u) u at hposN1
    rw [hm, mul_zero] at hposN1
    exact (lt_irrefl 0) hposN1
  rw [hformulaN, hformulaN1, inv_div]
  norm_num [Nat.factorial_succ]
  field_simp [hmN1]
  <;> ring

local instance effectiveVisibleEdgeSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance effectiveVisibleEdgeSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance effectiveVisibleEdgeSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance effectiveVisibleEdgeSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance effectiveVisibleEdgeSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance effectiveVisibleEdgeSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _
local instance effectiveVisibleEdgeSpatialSliceHaarSFinite
    (H N : ℕ) : SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance
local instance effectiveVisibleEdgePairHilbertSectorComplete
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    CompleteSpace (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete H N hN beta hbeta
local instance effectiveVisibleEdgeSpectralSupportNormedSpace
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    NormedSpace ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
  infer_instance
local instance effectiveVisibleEdgeSpectralSupportComplete
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
  exact (realHilbertZeroEigenspaceSupport_isClosed
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
      H N hN beta hbeta 1)).completeSpace_coe

/-- The asymptotic effective energy is exactly the lower logarithmic spectral
edge visible to the state. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_effectiveEnergyLimit_eq_visibleLogEnergyInf
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta) (hv : v ≠ 0) (lambda : ℝ)
    (hlambda : |lambda| < 2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_effectiveEnergyLimit
        H N hN beta hbeta v lambda =
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportVisibleLogEnergyInf
        H N hN beta hbeta v := by
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
    H N hN beta hbeta 1
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
  have hLower : ∀ mu : Eigenvalues
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)),
      c ≤ realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu := by
    intro mu
    simpa [T, c,
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportRestriction,
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralLogEnergy,
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralLogEnergy_ge_two_mul_finiteVolumeDecayRate
        H N hN beta hbeta mu)
  have hNormNative : ∀ x : (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive).domain,
      c * ‖(x : realHilbertZeroEigenspaceSupport T)‖ ≤
        ‖realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive x‖ := by
    rw [hGenerator]
    exact hNorm
  have hKerNative : ∀ x : (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive).domain,
      realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive x = 0 → x = 0 := by
    rw [hGenerator]
    exact hKer
  have hSurjNative : Function.Surjective
      (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive).toFun := by
    rw [hGenerator]
    exact hSurj
  have hQuadNative : ∀ x : (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive).domain,
      c * ‖(x : realHilbertZeroEigenspaceSupport T)‖ ^ 2 ≤
        inner ℝ (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive x)
          (x : realHilbertZeroEigenspaceSupport T) := by
    rw [hGenerator]
    exact hQuad
  let vNative : realHilbertZeroEigenspaceSupport T := by
    simpa [T,
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport] using v
  have hvNative : vNative ≠ 0 := by
    intro hz
    apply hv
    simpa [vNative, T,
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport] using hz
  have hVisibleRaw :=
    realHilbertCompactPositiveZeroSupportLogGenerator_ambientResolvent_effectiveEnergy_tendsto_visibleEnergyInf
      (E := periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector H N hN beta hbeta)
      T hCompact hPositive c hc hLower hNormNative hKerNative hSurjNative hQuadNative
      vNative hvNative lambda (by simpa [c] using hlambda)
  let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
    A c hc hNorm hKer hSurj lambda
  have hVisible : Tendsto
      (fun n : ℕ => lambda + inner ℝ ((F ^ (n + 1)) v) v / inner ℝ ((F ^ (n + 2)) v) v)
      atTop
      (𝓝 (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportVisibleLogEnergyInf
        H N hN beta hbeta v)) := by
    simpa [F, hGenerator, vNative,
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportVisibleLogEnergyInf,
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportVisibleLogEnergySet,
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport,
      T, hCompact, hPositive] using hVisibleRaw
  let q := periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
    H N hN beta hbeta v
  let rho := fun n : ℕ => lambda +
    (iteratedDeriv (n + 1) q lambda / ((n + 1 : ℝ) * iteratedDeriv n q lambda))⁻¹
  have hrhoPoint : ∀ n : ℕ,
      rho n = lambda + inner ℝ ((F ^ (n + 1)) v) v / inner ℝ ((F ^ (n + 2)) v) v := by
    intro n
    have h := realLinearPMapAmbientResolventQuadraticAmplitude_effectiveEnergy_eq_powInnerRatio
      A c hc hNorm hKer hSurj hSelfNative hQuad v hv n lambda
      (by simpa [c] using hlambda)
    simpa [rho, q, F,
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude,
      A, c] using h
  have hVisibleRho : Tendsto rho atTop
      (𝓝 (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportVisibleLogEnergyInf
        H N hN beta hbeta v)) := by
    rw [show rho = (fun n : ℕ => lambda +
      inner ℝ ((F ^ (n + 1)) v) v / inner ℝ ((F ^ (n + 2)) v) v) by
        funext n
        exact hrhoPoint n]
    exact hVisible
  have hEffective : Tendsto rho atTop
      (𝓝 (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_effectiveEnergyLimit
        H N hN beta hbeta v lambda)) := by
    simpa [rho, q] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_tendsto_effectiveEnergyLimit
        H N hN beta hbeta v hv lambda hlambda)
  exact tendsto_nhds_unique hEffective hVisibleRho

/-- Consequently the asymptotic effective energy is independent of the
admissible resolvent parameter. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_effectiveEnergyLimit_parameter_independent
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta) (hv : v ≠ 0) (lambda mu : ℝ)
    (hlambda : |lambda| < 2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
      H N hN beta hbeta)
    (hmu : |mu| < 2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_effectiveEnergyLimit
        H N hN beta hbeta v lambda =
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_effectiveEnergyLimit
        H N hN beta hbeta v mu := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_effectiveEnergyLimit_eq_visibleLogEnergyInf
      H N hN beta hbeta v hv lambda hlambda,
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_effectiveEnergyLimit_eq_visibleLogEnergyInf
      H N hN beta hbeta v hv mu hmu]

end

end MathlibAnalytic
end MGAP4D
