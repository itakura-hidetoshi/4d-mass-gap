import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFundamentalMatrixMomentDeterminantV5_NH
import Mathlib.Tactic

/-!
# P4-Q2-NI — authentic Wilson–Perron signed density cannot be a Dirac source

NH reduced the true nonconstancy question to a fundamental SU(2)
temporal exponential-kernel transform of the SAME original signed
two-interacting-Wilson-posterior coefficient rho. NI isolates the
first non-formal analytical obstruction without assuming injectivity.

1. Prove rho is a continuous function on the ACTUAL compact SU(2).
   The proof reconstructs rho pointwise as the authentic JH continuous
   original full-Wilson physical fiber divided by the strictly
   positive unchanged original full kernel and NG temporal factor.
2. At every beta>0 the two real rho signs survive the original
   right-spatial touching-plaquette factor and inverse Perron
   half-density, so the ordinary Haar integral of rho^2 is POSITIVE.
3. For EVERY y in SU(2) construct an explicit continuous test f
   vanishing at y but with integral f(g) rho(g) dHaar(g) NONZERO:
   use the positive lobe if rho(y)<0, negative lobe otherwise.
   Thus the original absolutely continuous signed density functional
   is NOT c times Dirac evaluation at y for ANY real c, even c=0.

This is an unconditional signed-measure/point-evaluation distinction.
It is NOT YET the nonconstancy of the exponential Wilson transform:
the remaining step is PROVING that this genuine SU(2) temporal
exponential kernel separates the just-constructed signed functional
from Dirac.  No injectivity/rank assumption is inserted, no new
physical source or detector is substituted and no fake posterior is
used.  No Dobrushin, sorry, admit, new axiom or mass-gap claim.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2NI_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2NI_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2NI_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2NI_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2NI_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2NI_openPosHaar :
    Measure.IsOpenPosMeasure
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  dsimp [normalizedCompactHaar]
  infer_instance

namespace GroundStatePosteriorJoint

local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ

private theorem p4Q2NI_max_mul_self_nonneg (a : ℝ) :
    0 ≤ max a 0 * a := by
  rcases le_total a 0 with h | h
  · rw [max_eq_right h]
    simp
  · rw [max_eq_left h]
    exact mul_nonneg h h

private theorem p4Q2NI_max_mul_self_pos (a : ℝ) (ha : 0 < a) :
    0 < max a 0 * a := by
  rw [max_eq_left ha.le]
  exact mul_pos ha ha

section OriginalSignedDensity
variable (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "mu" => normalizedCompactHaar Gauge
local notation "K" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 b
local notation "s" => continuousJointSqrtDensity H 2 (by norm_num) b hb
local notation "D" => p4Q2GB_originalWilsonPosteriorLeftDensityContrast H b hb
local notation "rho" => p4Q2NG_originalSpatialPerronSignedContrast H b hb
local notation "temp" => p4Q2NG_originalTemporalCharacterFactor b
local notation "k" => p4Q2JH_originalFiberKernel H b hb
include hb

/-- Continuity of the ACTUAL Wilson–Perron signed rho. Its proof is
deduced from the already established authentic continuous JH fiber,
the exact original one-link Wilson-K factorization, and the true
positive temporal SU(2) character. Not a replacement signed law. -/
theorem p4Q2NI_originalSpatialPerronSignedContrast_continuous
    (e : Link) (z : Cfg × Cfg) :
    Continuous (rho e z) := by
  let A : Cfg := fun _ => 1
  have hk : Continuous (fun g : Gauge => k e z (g,A)) :=
    (k e z).continuous.comp (continuous_id.prodMk continuous_const)
  have hShift : Continuous (fun g : Gauge => (A e)⁻¹ * g) :=
    continuous_const.mul continuous_id
  have hChar : Continuous
      (fun g : Gauge => p4Q2NG_originalSU2TemporalCharacter (A e) g) := by
    unfold p4Q2NG_originalSU2TemporalCharacter
    exact continuous_const.sub
      ((continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp hShift)
  have hTemp : Continuous (fun g : Gauge => temp (A e) (z.2 e) g) := by
    unfold p4Q2NG_originalTemporalCharacterFactor
    exact Real.continuous_exp.comp
      (continuous_const.mul (hChar.sub continuous_const))
  have hKpos : 0 < K A z.2 :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
      H 2 b A z.2
  have hFactor (g : Gauge) :
      0 < K A z.2 * temp (A e) (z.2 e) g :=
    mul_pos hKpos (Real.exp_pos _)
  have hkRatio (g : Gauge) :
      k e z (g,A) =
        (K A z.2 * temp (A e) (z.2 e) g) * rho e z g := by
    change
      K A (Function.update z.2 e g) *
          (s (z.1, Function.update z.2 e g))⁻¹ * D z.2 e g =
        (K A z.2 * temp (A e) (z.2 e) g) * rho e z g
    rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_update_right_eq_localFactor_mul
          H 2 b A z.2 e g,
        p4Q2NG_originalLocalFactor_eq_temporalCharacter_mul_spatial]
    unfold p4Q2NG_originalSpatialPerronSignedContrast
    ring
  have hContQuot : Continuous
      (fun g : Gauge =>
        (k e z (g,A)) / (K A z.2 * temp (A e) (z.2 e) g)) :=
    hk.div (continuous_const.mul hTemp) (fun g => (hFactor g).ne')
  have hEq : (fun g : Gauge => rho e z g) =
      (fun g : Gauge =>
        (k e z (g,A)) / (K A z.2 * temp (A e) (z.2 e) g)) := by
    funext g
    apply (eq_div_iff (hFactor g).ne').mpr
    calc
      rho e z g * (K A z.2 * temp (A e) (z.2 e) g) =
          (K A z.2 * temp (A e) (z.2 e) g) * rho e z g := by ring
      _ = k e z (g,A) := (hkRatio g).symm
  rw [hEq]
  exact hContQuot

/-- The authentic positive-beta Wilson–Perron signed density has a
strictly positive Haar square norm. This is unconditional but does NOT
assert positive variance of its exponential SU(2) convolution. -/
theorem p4Q2NI_originalSpatialPerronSignedContrast_HaarSq_pos
    (bpos : 0 < b) (e : Link) (z : Cfg × Cfg) :
    0 < ∫ g : Gauge, (rho e z g)^2 ∂mu := by
  have hr := p4Q2NI_originalSpatialPerronSignedContrast_continuous
    H b hb e z
  obtain ⟨⟨g,hg⟩, _⟩ :=
    p4Q2NH_originalSpatialPerronSignedContrast_has_both_signs
      H b hb bpos e z
  have hCont : Continuous (fun g : Gauge => (rho e z g)^2) := hr.pow 2
  have hInt : Integrable (fun g : Gauge => (rho e z g)^2) mu :=
    hCont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hNonzero : (rho e z g)^2 ≠ 0 :=
    pow_ne_zero 2 hg.ne'
  exact integral_pos_of_integrable_nonneg_nonzero hCont hInt
    (fun g => sq_nonneg _) hNonzero

/-- The original signed two-Wilson-posterior Perron density differs
from EVERY point evaluation functional on the real continuous
functions C(SU(2), R): a concrete test vanishes at the chosen boundary
point y but has nonzero signed Haar pairing with rho.

Test: negative rho lobe if rho(y)>=0, positive rho lobe otherwise.
The test is solely an analytical certificate of measure separation,
NOT a fabricated physical gauge-invariant source/detector. -/
theorem p4Q2NI_originalSpatialPerronSignedContrast_separates_Dirac
    (bpos : 0 < b) (e : Link) (z : Cfg × Cfg) (y : Gauge) :
    ∃ f : C(Gauge,ℝ),
      f y = 0 ∧ (∫ g : Gauge, f g * rho e z g ∂mu) ≠ 0 := by
  have hr : Continuous (rho e z) :=
    p4Q2NI_originalSpatialPerronSignedContrast_continuous H b hb e z
  obtain ⟨⟨gPos,hPos⟩, ⟨gNeg,hNeg⟩⟩ :=
    p4Q2NH_originalSpatialPerronSignedContrast_has_both_signs
      H b hb bpos e z
  by_cases hy : 0 ≤ rho e z y
  · let f : C(Gauge,ℝ) :=
      ⟨fun g => max (-(rho e z g)) 0, hr.neg.max continuous_const⟩
    refine ⟨f, ?_, ?_⟩
    · change max (-(rho e z y)) 0 = 0
      rw [max_eq_right (neg_nonpos.mpr hy)]
    · let F : Gauge → ℝ :=
        fun g => max (-(rho e z g)) 0 * (-(rho e z g))
      have hFcont : Continuous F :=
        (hr.neg.max continuous_const).mul hr.neg
      have hFint : Integrable F mu :=
        hFcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      have hFpos : 0 < F gNeg :=
        p4Q2NI_max_mul_self_pos _ (neg_pos.mpr hNeg)
      have hIntegral : 0 < ∫ g : Gauge, F g ∂mu :=
        integral_pos_of_integrable_nonneg_nonzero hFcont hFint
          (fun g => p4Q2NI_max_mul_self_nonneg _) hFpos.ne'
      have hEq :
          (∫ g : Gauge, f g * rho e z g ∂mu) =
            -(∫ g : Gauge, F g ∂mu) := by
        calc
          (∫ g : Gauge, f g * rho e z g ∂mu) =
              ∫ g : Gauge, -(F g) ∂mu := by
                apply integral_congr_ae
                filter_upwards with g
                change
                  max (-(rho e z g)) 0 * rho e z g =
                    -(max (-(rho e z g)) 0 * (-(rho e z g)))
                ring
          _ = -(∫ g : Gauge, F g ∂mu) := integral_neg
      rw [hEq]
      exact (neg_ne_zero.mpr hIntegral.ne')
  · have hyNeg : rho e z y < 0 := lt_of_not_ge hy
    let f : C(Gauge,ℝ) :=
      ⟨fun g => max (rho e z g) 0, hr.max continuous_const⟩
    refine ⟨f, ?_, ?_⟩
    · change max (rho e z y) 0 = 0
      rw [max_eq_right hyNeg.le]
    · let F : Gauge → ℝ :=
        fun g => max (rho e z g) 0 * rho e z g
      have hFcont : Continuous F :=
        (hr.max continuous_const).mul hr
      have hFint : Integrable F mu :=
        hFcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      have hFpos : 0 < F gPos :=
        p4Q2NI_max_mul_self_pos _ hPos
      have hIntegral : 0 < ∫ g : Gauge, F g ∂mu :=
        integral_pos_of_integrable_nonneg_nonzero hFcont hFint
          (fun g => p4Q2NI_max_mul_self_nonneg _) hFpos.ne'
      change (∫ g : Gauge, F g ∂mu) ≠ 0
      exact hIntegral.ne'

/-- Strengthened genuine signed-measure obstruction: the original
Wilson–Perron rho pairing cannot equal ANY real multiple of
evaluation at the selected right-link group element. This is proved
from an EXPLICIT CONTINUOUS signed-lobe witness, not by assuming
injectivity of NG's temporal kernel or the nonzero determinant. -/
theorem p4Q2NI_originalSpatialPerronSignedContrast_not_pointEvaluation
    (bpos : 0 < b) (e : Link) (z : Cfg × Cfg)
    (y : Gauge) (c : ℝ) :
    ∃ f : C(Gauge,ℝ),
      (∫ g : Gauge, f g * rho e z g ∂mu) ≠ c * f y := by
  obtain ⟨f,hfy,hInt⟩ :=
    p4Q2NI_originalSpatialPerronSignedContrast_separates_Dirac
      H b hb bpos e z y
  refine ⟨f, ?_⟩
  simpa [hfy] using hInt

/-- Apply the preceding unconditional functional separation to the
ACTUAL original right-boundary source y=z.right(e), precisely the
point mass that appears on the right side of NG/NH. -/
theorem p4Q2NI_originalWilsonBoundarySignedDensity_not_Dirac
    (bpos : 0 < b) (e : Link) (z : Cfg × Cfg) (c : ℝ) :
    ∃ f : C(Gauge,ℝ),
      (∫ g : Gauge, f g * rho e z g ∂mu) ≠ c * f (z.2 e) :=
  p4Q2NI_originalSpatialPerronSignedContrast_not_pointEvaluation
    H b hb bpos e z (z.2 e) c

end OriginalSignedDensity
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NI_originalSpatialPerronSignedContrast_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NI_originalSpatialPerronSignedContrast_HaarSq_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NI_originalSpatialPerronSignedContrast_separates_Dirac
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NI_originalSpatialPerronSignedContrast_not_pointEvaluation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NI_originalWilsonBoundarySignedDensity_not_Dirac
