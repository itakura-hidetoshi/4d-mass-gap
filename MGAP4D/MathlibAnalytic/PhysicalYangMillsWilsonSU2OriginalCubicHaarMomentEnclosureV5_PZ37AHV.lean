import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalGaugeWardCenterMixedHaarExactV5_PZ37AHU
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AHV — original cubic Haar moment enclosures and symmetry obstruction

AHU proved the TRUE mixed Haar correlation Y_H(B) = p_H V_H and
  M2_H(B) = M3_H + (3*p_H + W_H(B))*V_H,
where M3_H is the still-uncomputed original spatial product-Haar cubic
moment of the unmodified signed ZW Gauss-law source f_H.

This leaf first obtains genuinely unconditional inequalities ONLY from
AGN's original pointwise amplitude |f_H(A)| <= p_H/2, AHN's original
positive Haar second source moment V_H, and original compact Haar
integrability:

 -(p_H/2)*V_H <= M3_H <= (p_H/2)*V_H.

Therefore the original signed-source, true full-Wilson second-action
moment has the positive strict finite-volume lower bound

 (5*p_H/2 + W_H(B))*V_H <= M2_H(B)
                         <= (7*p_H/2 + W_H(B))*V_H.

No hidden sign choice for M3_H is made.

The final theorem isolates the precise *additional* geometry required
for the strictly stronger claim M3_H=0: a TRUE original spatial-Haar
measure-preserving configuration transformation T with
f_H(T(A))=-f_H(A). This is a conditional implication, not an assumed
construction or a declaration that a putative Z2 twist already exists.
It records the descent obstruction for the next genuine finite
even-periodic center-twist construction.

No changes to any original SU(2) physical one-slab kernel, both
spatial halfweights, true product Haar, source, Wilson action,
pinned toolchain, original Type-valued proof history, or old Lean files.
Fixed beta0 sign, H-uniform coercivity, Hamiltonian spectral gap and
continuum 4D YM gap are NOT claimed.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AHV_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AHV_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AHV_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AHV_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AHV_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muH" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "fCont" => p4Q2PZ37AFZ_originalCenteredContinuous H
local notation "pH" => p4Q2PZ37AFZ_plaquetteCount H
local notation "Vsrc" => p4Q2PZ37AHN_originalSource_HaarSecondMoment H
local notation "M3" => p4Q2PZ37AHS_originalSourceThirdHaarMoment H
local notation "M2" => p4Q2PZ37AHS_originalSecondFullActionHaarMoment H
local notation "W" => periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2

local instance p4Q2PZ37AHV_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- The original pointwise centered ZW source amplitude controls BOTH
signs of its genuine cubic integrand, without asserting an odd symmetry. -/
theorem p4Q2PZ37AHV_originalSourceCube_pointwiseInterval (A : Cfg) :
    -(pH / 2) * (fCont A)^2 ≤ (fCont A)^3 ∧
      (fCont A)^3 ≤ (pH / 2) * (fCont A)^2 := by
  have hAbs : |fCont A| ≤ pH / 2 :=
    p4Q2PZ37AGN_originalContinuousSource_abs_le_halfCount H A
  obtain ⟨hLo, hHi⟩ := abs_le.mp hAbs
  have hSq : 0 ≤ (fCont A)^2 := sq_nonneg _
  constructor
  · calc
      -(pH / 2) * (fCont A)^2 ≤ fCont A * (fCont A)^2 :=
        mul_le_mul_of_nonneg_right hLo hSq
      _ = (fCont A)^3 := by ring
  · calc
      (fCont A)^3 = fCont A * (fCont A)^2 := by ring
      _ ≤ (pH / 2) * (fCont A)^2 :=
        mul_le_mul_of_nonneg_right hHi hSq

/-- The true original signed-source cubic is integrable over the
unmodified compact spatial SU(2) product Haar probability. -/
theorem p4Q2PZ37AHV_originalSourceCube_integrable :
    Integrable (fun A : Cfg => (fCont A)^3) muH := by
  exact (((p4Q2PZ37AFZ_originalCenteredContinuous H).continuous.pow 3)
    .integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

/-- The authentic still-unevaluated source cubic Haar moment lies in a
two-sided true-moment enclosure. The bounds do not presume a sign for
M3_H or replace either original Wilson posterior. -/
theorem p4Q2PZ37AHV_originalSourceThirdMoment_interval :
    -(pH / 2) * Vsrc ≤ M3 ∧ M3 ≤ (pH / 2) * Vsrc := by
  have hf : Continuous (fun A : Cfg => fCont A) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous
  have hCubic : Integrable (fun A : Cfg => (fCont A)^3) muH :=
    p4Q2PZ37AHV_originalSourceCube_integrable H
  have hLow : Integrable
      (fun A : Cfg => -(pH / 2) * (fCont A)^2) muH :=
    (continuous_const.mul (hf.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hHigh : Integrable
      (fun A : Cfg => (pH / 2) * (fCont A)^2) muH :=
    (continuous_const.mul (hf.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  constructor
  · calc
      -(pH / 2) * Vsrc =
          (∫ A : Cfg, -(pH / 2) * (fCont A)^2 ∂muH) := by
        rw [integral_const_mul]
        rfl
      _ ≤ (∫ A : Cfg, (fCont A)^3 ∂muH) :=
        integral_mono hLow hCubic
          (fun A => (p4Q2PZ37AHV_originalSourceCube_pointwiseInterval H A).1)
      _ = M3 := rfl
  · calc
      M3 = (∫ A : Cfg, (fCont A)^3 ∂muH) := rfl
      _ ≤ (∫ A : Cfg, (pH / 2) * (fCont A)^2 ∂muH) :=
        integral_mono hCubic hHigh
          (fun A => (p4Q2PZ37AHV_originalSourceCube_pointwiseInterval H A).2)
      _ = (pH / 2) * Vsrc := by
        rw [integral_const_mul]
        rfl

/-- A true signed absolute cubic-Haar-moment budget; in particular,
the AHU unknown cubic intercept correction is quantitatively small
relative to the original source second moment. -/
theorem p4Q2PZ37AHV_originalSourceThirdMoment_absBudget :
    |M3| ≤ (pH / 2) * Vsrc := by
  have h := p4Q2PZ37AHV_originalSourceThirdMoment_interval H
  exact abs_le.mpr ⟨by simpa only [neg_mul] using h.1, h.2⟩

/-- The complete actual source-weighted full-Wilson second-action moment
is trapped between two explicit affine original Wilson-action profiles.
All original temporal crossing terms remain inside M2_H. -/
theorem p4Q2PZ37AHV_originalSecondFullActionMoment_interval
    (B : Cfg) :
    (5 * pH / 2 + W B) * Vsrc ≤ M2 B ∧
      M2 B ≤ (7 * pH / 2 + W B) * Vsrc := by
  have h := p4Q2PZ37AHV_originalSourceThirdMoment_interval H
  have hExact := p4Q2PZ37AHU_originalSecondFullActionMoment_exactMixed H B
  constructor
  · calc
      (5 * pH / 2 + W B) * Vsrc =
          -(pH / 2) * Vsrc + (3 * pH + W B) * Vsrc := by ring
      _ ≤ M3 + (3 * pH + W B) * Vsrc :=
        add_le_add_left h.1 _
      _ = M2 B := hExact.symm
  · calc
      M2 B = M3 + (3 * pH + W B) * Vsrc := hExact
      _ ≤ (pH / 2) * Vsrc + (3 * pH + W B) * Vsrc :=
        add_le_add_left h.2 _
      _ = (7 * pH / 2 + W B) * Vsrc := by ring

/-- Unlike a sign assertion about the transfer, this is a proved
STRICT positivity theorem for the genuine source-weighted second
one-slab ACTION moment at every true finite H and right boundary. -/
theorem p4Q2PZ37AHV_originalSecondFullActionMoment_pos
    (B : Cfg) : 0 < M2 B := by
  have hp : 0 < pH := p4Q2PZ37AHN_count_pos H
  have hv : 0 < Vsrc :=
    (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2
  have hw : 0 ≤ W B :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_nonneg
      H 2 (by norm_num) B
  have hc : 0 < 5 * pH / 2 + W B := by
    linarith only [hp, hw]
  exact lt_of_lt_of_le (mul_pos hc hv)
    (p4Q2PZ37AHV_originalSecondFullActionMoment_interval H B).1

/-- An exact reduction of the cubic moment to the *additional* existence
of a true source-odd Haar-preserving map. This does NOT postulate that
such a map has been constructed; constructing the true global Z2 center
twist and proving its plaquette sign is the next independent task. -/
theorem p4Q2PZ37AHV_originalSourceThirdMoment_zero_of_oddHaar
    (T : Cfg → Cfg)
    (hT : MeasurePreserving T muH muH)
    (hOdd : ∀ A : Cfg, fCont (T A) = -(fCont A)) :
    M3 = 0 := by
  have hCube : Continuous (fun A : Cfg => (fCont A)^3) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous.pow 3
  have hMeas : AEStronglyMeasurable
      (fun A : Cfg => (fCont A)^3) muH :=
    hCube.measurable.aestronglyMeasurable
  have hMap : Measure.map T muH = muH := hT.map_eq
  have hMeasMap : AEStronglyMeasurable
      (fun A : Cfg => (fCont A)^3) (Measure.map T muH) := by
    rw [hMap]
    exact hMeas
  have hIntMap :
      (∫ A : Cfg, (fCont (T A))^3 ∂muH) =
        (∫ A : Cfg, (fCont A)^3 ∂muH) := by
    calc
      (∫ A : Cfg, (fCont (T A))^3 ∂muH) =
          ∫ A : Cfg, (fCont A)^3 ∂Measure.map T muH := by
        symm
        exact MeasureTheory.integral_map hT.measurable.aemeasurable hMeasMap
      _ = (∫ A : Cfg, (fCont A)^3 ∂muH) := by rw [hMap]
  have hIntOdd :
      (∫ A : Cfg, (fCont (T A))^3 ∂muH) =
        -(∫ A : Cfg, (fCont A)^3 ∂muH) := by
    calc
      (∫ A : Cfg, (fCont (T A))^3 ∂muH) =
          (∫ A : Cfg, -((fCont A)^3) ∂muH) := by
        apply integral_congr_ae
        filter_upwards with A
        rw [hOdd A]
        ring
      _ = -(∫ A : Cfg, (fCont A)^3 ∂muH) := by
        rw [integral_neg]
  have hEq :
      (∫ A : Cfg, (fCont A)^3 ∂muH) =
        -(∫ A : Cfg, (fCont A)^3 ∂muH) :=
    hIntMap.symm.trans hIntOdd
  change (∫ A : Cfg, (fCont A)^3 ∂muH) = 0
  linarith only [hEq]

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHV_originalSourceCube_pointwiseInterval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHV_originalSourceCube_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHV_originalSourceThirdMoment_interval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHV_originalSourceThirdMoment_absBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHV_originalSecondFullActionMoment_interval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHV_originalSecondFullActionMoment_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHV_originalSourceThirdMoment_zero_of_oddHaar
