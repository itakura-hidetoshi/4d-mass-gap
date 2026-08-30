import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorResolventQuadraticAbsoluteMonotonicityConcrete
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End Filter
open scoped InnerProductSpace LinearPMap Topology BigOperators

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

universe u

/-- Strict quadratic positivity of the bounded ambient resolvent on every
nonzero vector.  The proof uses an actual-domain preimage of the test vector:
coercivity leaves the strictly positive margin `c - λ`, while the two-sided
resolvent identity forces that preimage to be nonzero whenever the test vector
is nonzero.  The forward operator remains partially defined. -/
theorem realLinearPMapAmbientResolventFamily_inner_pos_of_quadratic_lower_bound
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun)
    (hQuad : ∀ x : A.domain,
      c * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E))
    (lambda : ℝ)
    (hlambda : |lambda| < c)
    (y : E)
    (hy : y ≠ 0) :
    0 < inner ℝ
      (realLinearPMapAmbientResolventFamily_of_norm_lower_bound
        A c hc hNorm hKer hSurj lambda y)
      y := by
  let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
    A c hc hNorm hKer hSurj
  rcases realLinearPMapAmbientResolventFamily_exists_domain_preimage
      A c hc hNorm hKer hSurj lambda hlambda y with
    ⟨x, hxy, hFx⟩
  have hlambda' : lambda < c := lt_of_le_of_lt (le_abs_self lambda) hlambda
  have hx : x ≠ 0 := by
    intro hx
    apply hy
    rw [← hxy, hx]
    rfl
  have hxcoe : (x : E) ≠ 0 := by
    intro hx0
    apply hx
    apply Subtype.ext
    exact hx0
  have hxnorm : 0 < ‖(x : E)‖ := norm_pos_iff.mpr hxcoe
  have hq := hQuad x
  change 0 < inner ℝ (F lambda y) y
  rw [hFx, ← hxy, real_inner_comm]
  change 0 < inner ℝ (A x - lambda • (x : E)) (x : E)
  rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  nlinarith [sq_pos_of_pos hxnorm]

local instance supportResolventStrictSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance supportResolventStrictSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance supportResolventStrictSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance supportResolventStrictSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance supportResolventStrictSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance supportResolventStrictSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance supportResolventStrictSpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance supportResolventStrictPairHilbertSectorComplete
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    H N hN beta hbeta

/-- Physical specialization: on the actual one-step positive spectral support,
the bounded logarithmic resolvent has a strictly positive diagonal quadratic
form for every nonzero state throughout the full symmetric coercive gap. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (u :
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta)
    (hu : u ≠ 0)
    (lambda : ℝ)
    (hlambda :
      |lambda| <
        2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta) :
    0 <
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
        H N hN beta hbeta u lambda := by
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
  have hpos :=
    realLinearPMapAmbientResolventFamily_inner_pos_of_quadratic_lower_bound
      A c hc
      (by
        intro x
        simpa [A, c] using
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_norm_lower_bound
            H N hN beta hbeta x))
      (by
        intro x hx
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_eq_zero_of_apply_eq_zero
            H N hN beta hbeta x hx)
      (by
        simpa [A] using
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_surjective
            H N hN beta hbeta))
      (by
        intro x
        simpa [A, c] using
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_quadratic_lower_bound
            H N hN beta hbeta x))
      lambda (by simpa [c] using hlambda) u hu
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude,
    A, c] using hpos

end

end MathlibAnalytic
end MGAP4D
