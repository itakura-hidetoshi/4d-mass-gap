import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalExponentialHaarStrictPosV5_KU
import Mathlib.Tactic

/-!
# P4-Q2-KV — ACTUAL positive-beta SU(2) Wilson one-link Haar integral
# transform injectivity for every continuous real signed source

KU has proved strict positive double-Haar quadratic energy for the
exact full SU(2) real-feature exponential, by transporting the
original finite positive Taylor energies through the genuine
uniform Banach series. The literal one-plaquette original Wilson
relative kernel is the positive exp(-b) scalar times that exact
feature exponential with t=b/2. This is an identity of the
ORIGINAL Wilson action, not an auxiliary or replacement kernel.

We now conclude directly:
 (∀g, ∫h K_b(g,h) ψ(h) dν(h)=0) -> ψ=0,
at every frozen positive b and for every continuous signed ψ.
Equivalently any nonzero continuous signed source is detected at
SOME actual SU(2) right-link value by the original Wilson
one-link Haar kernel integral transform.

The original normalized Haar is only the reference measure; it
does not replace EITHER of the genuinely interacting conditional
Wilson posteriors. This does not yet prove the true two-posterior
physical GI second-context response is nonzero, the full lattice
Wilson transfer operator is injective, H1-C3 strong closure, or
the continuum 4d Yang–Mills mass gap. No sorry/admit/new axioms,
no arbitrary rank/source-frame assumptions.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2KV_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2KV_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2KV_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2KV_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2KV_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section SU2
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Phi" => specialUnitaryMatrixRealFeature 2
local notation "nu" => normalizedCompactHaar Gauge
local notation "nuPair" => Measure.prod (normalizedCompactHaar Gauge) (normalizedCompactHaar Gauge)
local notation "Exp" => p4Q2KR_originalSU2FeatureExponentialContinuous

/-- The LITERAL original SU(2) Wilson relative Boltzmann kernel is a
STRICTLY POSITIVE constant multiple of KU's proved injective full
exponential real-matrix-feature kernel; the exact scale is b/2. -/
theorem p4Q2KV_originalWilsonRelativeKernel_eq_realFeatureExponential
    (b : ℝ) (g h : Gauge) :
    specialUnitaryWilsonRelativeKernel 2 b g h =
      Real.exp (-b) * Exp (b / 2) (g,h) := by
  rw [specialUnitaryWilsonRelativeKernel_eq_trace,
    p4Q2KR_originalSU2FeatureExponentialContinuous_apply,
    specialUnitaryNormalizedTraceRelativeKernel_eq_scaled,
    specialUnitaryRealTraceRelativeKernel_eq_inner]
  congr 1
  congr 1
  ring

/-- An actual SU(2) Wilson positive-coupling one-link Haar
CONVOLUTION kernel has no nonzero continuous signed source in its
nullspace. Proven from KU's strictly positive original exponential
quadratic energy and literal Fubini of continuous integrands. -/
theorem p4Q2KV_originalWilsonSingleLinkHaarTransform_injective
    (b : ℝ) (hb : 0 < b) (ψ : C(Gauge, ℝ))
    (hzero : ∀ g : Gauge,
      (∫ h : Gauge, specialUnitaryWilsonRelativeKernel 2 b g h * ψ h ∂nu) = 0) :
    ψ = 0 := by
  by_contra hψ
  let W : C(Gauge × Gauge, ℝ) := Exp (b / 2)
  have hExpZero (g : Gauge) :
      (∫ h : Gauge, W (g,h) * ψ h ∂nu) = 0 := by
    have hFactor :
        (∫ h : Gauge, specialUnitaryWilsonRelativeKernel 2 b g h * ψ h ∂nu) =
          Real.exp (-b) * (∫ h : Gauge, W (g,h) * ψ h ∂nu) := by
      calc
        (∫ h : Gauge, specialUnitaryWilsonRelativeKernel 2 b g h * ψ h ∂nu) =
          ∫ h : Gauge, Real.exp (-b) * (W (g,h) * ψ h) ∂nu := by
            apply integral_congr_ae
            filter_upwards with h
            dsimp [W]
            rw [p4Q2KV_originalWilsonRelativeKernel_eq_realFeatureExponential]
            ring
        _ = Real.exp (-b) * (∫ h : Gauge, W (g,h) * ψ h ∂nu) :=
          integral_const_mul _ _
    have hZero := hzero g
    rw [hFactor] at hZero
    rcases mul_eq_zero.mp hZero with hBad | hGood
    · exact False.elim ((Real.exp_pos (-b)).ne' hBad)
    · exact hGood
  have hWCont : Continuous (fun p : Gauge × Gauge =>
      W p * (ψ p.1 * ψ p.2)) :=
    W.continuous.mul
      ((ψ.continuous.comp continuous_fst).mul
        (ψ.continuous.comp continuous_snd))
  have hWI :
      Integrable (fun p : Gauge × Gauge =>
        W p * (ψ p.1 * ψ p.2)) nuPair :=
    hWCont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hPairZero :
      p4Q2KU_originalSU2PairHaarMomentCLM ψ W = 0 := by
    calc
      p4Q2KU_originalSU2PairHaarMomentCLM ψ W =
          ∫ p : Gauge × Gauge,
            W p * (ψ p.1 * ψ p.2) ∂nuPair :=
        p4Q2KU_originalSU2PairHaarMomentCLM_apply ψ W
      _ = ∫ g : Gauge, ∫ h : Gauge,
          W (g,h) * (ψ g * ψ h) ∂nu ∂nu :=
        integral_prod _ hWI
      _ = ∫ g : Gauge, (0 : ℝ) ∂nu := by
        apply integral_congr_ae
        filter_upwards with g
        calc
          (∫ h : Gauge, W (g,h) * (ψ g * ψ h) ∂nu) =
              ∫ h : Gauge, ψ g * (W (g,h) * ψ h) ∂nu := by
            apply integral_congr_ae
            filter_upwards with h
            ring
          _ = ψ g * (∫ h : Gauge, W (g,h) * ψ h ∂nu) :=
            integral_const_mul _ _
          _ = 0 := by rw [hExpZero g]; ring
      _ = 0 := by simp
  have hStrict :
      0 < p4Q2KU_originalSU2PairHaarMomentCLM ψ W := by
    exact p4Q2KU_originalSU2WilsonExponentialHaarQuadratic_pos
      ψ hψ (b / 2) (by positivity)
  exact (ne_of_gt hStrict) hPairZero

/-- For every positive coupling and nonzero SU(2) real continuous
signed source, a TRUE right SU(2) Wilson kernel section detects it.
This is a theorem-produced witness, not a synthetic rank condition. -/
theorem p4Q2KV_originalWilsonSingleLinkHaarTransform_exists_nonzero_receiver
    (b : ℝ) (hb : 0 < b) (ψ : C(Gauge, ℝ)) (hψ : ψ ≠ 0) :
    ∃ g : Gauge,
      (∫ h : Gauge, specialUnitaryWilsonRelativeKernel 2 b g h *
        ψ h ∂nu) ≠ 0 := by
  by_contra hNone
  have hAll (g : Gauge) :
      (∫ h : Gauge, specialUnitaryWilsonRelativeKernel 2 b g h *
        ψ h ∂nu) = 0 := by
    by_contra hNonzero
    exact hNone ⟨g, hNonzero⟩
  exact hψ (p4Q2KV_originalWilsonSingleLinkHaarTransform_injective
    b hb ψ hAll)

end SU2
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KV_originalWilsonRelativeKernel_eq_realFeatureExponential
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KV_originalWilsonSingleLinkHaarTransform_injective
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KV_originalWilsonSingleLinkHaarTransform_exists_nonzero_receiver
