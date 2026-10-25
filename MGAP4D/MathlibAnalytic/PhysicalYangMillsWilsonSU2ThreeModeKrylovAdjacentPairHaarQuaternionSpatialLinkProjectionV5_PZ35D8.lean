import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarQuaternionEightOrbitV5_PZ35D7
import Mathlib.Tactic

/-!
# P4-Q2-PZ35D8 — original full spatial product-Haar single-link Schur projector

This is an exact identity in the actual ORIGINAL finite periodic SU(2)
spatial-link PRODUCT Haar measure. Use the eight actual SU(2) translations
at ONE original lattice link (PZ35D6) and the pointwise eight-orbit
quaternion/center projector (PZ35D7). Both link orientations work, for
ARBITRARY continuous factors independent of the translated coordinate.

The computation is not an integration with finite-subgroup counting
measure. The original product Haar measure and Wilson energy are
unchanged. Four successive applications to four distinct original
plaquette links are the separate remaining PZ35D9 step.

No new axiom, sorry, admit, native_decide, altered model/posterior.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "q" => p4Q2PZ35B_quaternionFamily
local notation "z" => p4Q2PZ35D4_centralMinusOne
local notation "χ" => p4Q2PZ35C_originalOneLinkCharacter
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2

local instance p4Q2PZ35D8_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance p4Q2PZ35D8_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2

local instance p4Q2PZ35D8_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2

local instance p4Q2PZ35D8_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2

local instance p4Q2PZ35D8_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

local instance p4Q2PZ35D8_probability :
    IsProbabilityMeasure (normalizedCompactHaar G) :=
  normalizedCompactHaar_isProbabilityMeasure G

local instance p4Q2PZ35D8_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

namespace GroundStatePosteriorJoint
section OriginalSpatialLinkProjection
variable (H : ℕ)

local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "T" => p4Q2PZ35D6_originalSpatialSingleLinkLeftTranslate H

/-- Genuine original one-link SU(2) translation is continuous
in the original finite product topology. -/
theorem p4Q2PZ35D8_originalSpatialLinkTranslation_continuous
    (target : Link) (a : G) :
    Continuous (T target a) := by
  apply continuous_pi
  intro e
  change Continuous (fun A : Cfg => if e = target then a * A e else A e)
  by_cases he : e = target
  · subst e
    simpa using (continuous_const.mul (continuous_apply target))
  · simpa [he] using (continuous_apply e)

/-- Eight translations in the true ORIGINAL spatial product Haar
preserve each integral, hence their SUM is eight times it. -/
theorem p4Q2PZ35D8_originalSpatialHaar_eightLinkIntegralAverage
    (target : Link) (f : Cfg → ℝ) (hf : Continuous f) :
    (∫ A : Cfg, (∑ j : Fin 4,
      (f (T target (q j) A) +
       f (T target (z * q j) A))) ∂haar) =
      8 * (∫ A : Cfg, f A ∂haar) := by
  have hInt (a : G) :
      Integrable (fun A : Cfg => f (T target a A)) haar := by
    have hc : Continuous (fun A : Cfg => f (T target a A)) :=
      hf.comp (p4Q2PZ35D8_originalSpatialLinkTranslation_continuous H target a)
    exact hc.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    (∫ A : Cfg, (∑ j : Fin 4,
      (f (T target (q j) A) + f (T target (z * q j) A))) ∂haar) =
      ∑ j : Fin 4, (∫ A : Cfg,
        (f (T target (q j) A) + f (T target (z * q j) A)) ∂haar) := by
        simpa using
          (integral_finset_sum (Finset.univ : Finset (Fin 4))
            (fun j _hj => (hInt (q j)).add (hInt (z * q j))))
    _ = ∑ j : Fin 4,
        ((∫ A : Cfg, f (T target (q j) A) ∂haar) +
         (∫ A : Cfg, f (T target (z * q j) A) ∂haar)) := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [integral_add (hInt (q j)) (hInt (z * q j))]
    _ = ∑ _j : Fin 4,
        ((∫ A : Cfg, f A ∂haar) + (∫ A : Cfg, f A ∂haar)) := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [p4Q2PZ35D6_originalSpatialHaar_oneLinkIntegralLeftTranslate
        H target (q j) f hf,
        p4Q2PZ35D6_originalSpatialHaar_oneLinkIntegralLeftTranslate
          H target (z * q j) f hf]
    _ = 8 * (∫ A : Cfg, f A ∂haar) := by
      simp only [Fin.sum_univ_four]
      ring

/-- The literal physical SU(2) Wilson character and energy
remain continuous on the original finite spatial slice. -/
private theorem p4Q2PZ35D8_originalCharacter_continuous :
    Continuous χ :=
  continuous_const.sub (continuous_specialUnitaryWilsonPlaquetteEnergy 2)

/-- One-link forward Schur contraction IN THE ORIGINAL FULL SPATIAL
PRODUCT HAAR: extra Wilson factors F and holonomy remainder c may
depend on every OTHER link, but do not change with this link. -/
theorem p4Q2PZ35D8_originalSpatialHaar_forwardProject
    (target : Link) (b : G) (c : Cfg → G) (F : Cfg → ℝ)
    (hc : Continuous c) (hF : Continuous F)
    (hcInv : ∀ (a : G) (A : Cfg), c (T target a A) = c A)
    (hFInv : ∀ (a : G) (A : Cfg), F (T target a A) = F A) :
    (∫ A : Cfg,
      (χ (A target * c A) * E ((A target)⁻¹ * b)) * F A ∂haar) =
      -(1 / 4 : ℝ) * (∫ A : Cfg,
        χ (b * c A) * F A ∂haar) := by
  let obs : Cfg → ℝ := fun A =>
    (χ (A target * c A) * E ((A target)⁻¹ * b)) * F A
  have hObs : Continuous obs := by
    have hChi : Continuous (fun A : Cfg => χ (A target * c A)) :=
      p4Q2PZ35D8_originalCharacter_continuous.comp
        ((continuous_apply target).mul hc)
    have hEnergy : Continuous (fun A : Cfg => E ((A target)⁻¹ * b)) :=
      (continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp
        ((continuous_apply target).inv.mul continuous_const)
    exact (hChi.mul hEnergy).mul hF
  have hTerm (a : G) (A : Cfg) :
      obs (T target a A) =
        (χ ((a * A target) * c A) * E ((a * A target)⁻¹ * b)) * F A := by
    change
      (χ ((T target a A) target * c (T target a A)) *
        E (((T target a A) target)⁻¹ * b)) * F (T target a A) = _
    rw [p4Q2PZ35D6_originalLinkTranslate_at H target a A,
      hcInv a A, hFInv a A]
  have hOrbit (A : Cfg) :
      (∑ j : Fin 4,
        (obs (T target (q j) A) +
         obs (T target (z * q j) A))) =
          -2 * (χ (b * c A) * F A) := by
    calc
      (∑ j : Fin 4,
        (obs (T target (q j) A) +
         obs (T target (z * q j) A))) =
        (∑ j : Fin 4,
          (χ (((q j) * A target) * c A) *
            E (((q j) * A target)⁻¹ * b) +
           χ (((z * q j) * A target) * c A) *
            E (((z * q j) * A target)⁻¹ * b))) * F A := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _hj
        rw [hTerm (q j) A, hTerm (z * q j) A]
        simp only [mul_assoc]
        ring
      _ = -2 * (χ (b * c A) * F A) := by
        have hg :
            (∑ j : Fin 4,
              (χ (((q j) * A target) * c A) *
                E (((q j) * A target)⁻¹ * b) +
               χ (((z * q j) * A target) * c A) *
                E (((z * q j) * A target)⁻¹ * b))) =
              -2 * χ (b * c A) := by
          simpa only [mul_assoc] using
            (p4Q2PZ35D7_originalEightOrbit_forward b (c A) (A target))
        rw [hg]
        ring
  have hAvg :=
    p4Q2PZ35D8_originalSpatialHaar_eightLinkIntegralAverage H target obs hObs
  have hIntegrals :
      (∫ A : Cfg,
        (∑ j : Fin 4,
          (obs (T target (q j) A) +
           obs (T target (z * q j) A))) ∂haar) =
      ∫ A : Cfg, -2 * (χ (b * c A) * F A) ∂haar := by
    apply integral_congr_ae
    filter_upwards with A
    exact hOrbit A
  rw [hIntegrals, integral_const_mul] at hAvg
  change (-2 : ℝ) * (∫ A : Cfg, χ (b * c A) * F A ∂haar) =
      8 * (∫ A : Cfg, obs A ∂haar) at hAvg
  change (∫ A : Cfg, obs A ∂haar) =
      -(1 / 4 : ℝ) * (∫ A : Cfg, χ (b * c A) * F A ∂haar)
  linarith

/-- Inverse-oriented projection on the SAME original full spatial Haar
follows from actual SU(2) character inversion and cyclic trace. -/
theorem p4Q2PZ35D8_originalSpatialHaar_inverseProject
    (target : Link) (b : G) (c : Cfg → G) (F : Cfg → ℝ)
    (hc : Continuous c) (hF : Continuous F)
    (hcInv : ∀ (a : G) (A : Cfg), c (T target a A) = c A)
    (hFInv : ∀ (a : G) (A : Cfg), F (T target a A) = F A) :
    (∫ A : Cfg,
      (χ ((A target)⁻¹ * c A) * E ((A target)⁻¹ * b)) * F A ∂haar) =
      -(1 / 4 : ℝ) * (∫ A : Cfg,
        χ (b⁻¹ * c A) * F A ∂haar) := by
  have hc' : Continuous (fun A : Cfg => (c A)⁻¹) := hc.inv
  have hcInv' : ∀ (a : G) (A : Cfg),
      (fun X : Cfg => (c X)⁻¹) (T target a A) = (c A)⁻¹ := by
    intro a A
    change (c (T target a A))⁻¹ = (c A)⁻¹
    rw [hcInv a A]
  have hResult :=
    p4Q2PZ35D8_originalSpatialHaar_forwardProject
      H target b (fun A : Cfg => (c A)⁻¹) F hc' hF hcInv' hFInv
  calc
    (∫ A : Cfg,
      (χ ((A target)⁻¹ * c A) * E ((A target)⁻¹ * b)) * F A ∂haar) =
      (∫ A : Cfg,
        (χ (A target * (c A)⁻¹) * E ((A target)⁻¹ * b)) * F A ∂haar) := by
      apply integral_congr_ae
      filter_upwards with A
      rw [p4Q2PZ35D7_originalInverseCharacter_as_forward]
    _ = -(1 / 4 : ℝ) * (∫ A : Cfg,
        χ (b * (c A)⁻¹) * F A ∂haar) := hResult
    _ = -(1 / 4 : ℝ) * (∫ A : Cfg,
        χ (b⁻¹ * c A) * F A ∂haar) := by
      congr 1
      apply integral_congr_ae
      filter_upwards with A
      have hInv :
          χ (b * (c A)⁻¹) = χ (b⁻¹ * c A) := by
        calc
          χ (b * (c A)⁻¹) = χ ((b * (c A)⁻¹)⁻¹) :=
            (p4Q2PZ35D5_originalCharacter_inv (b * (c A)⁻¹)).symm
          _ = χ (c A * b⁻¹) := by rw [mul_inv_rev, inv_inv]
          _ = χ (b⁻¹ * c A) :=
            p4Q2PZ35D5_originalCharacter_mul_comm (c A) b⁻¹
      rw [hInv]

end OriginalSpatialLinkProjection
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ35D8_originalSpatialLinkTranslation_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ35D8_originalSpatialHaar_eightLinkIntegralAverage
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ35D8_originalSpatialHaar_forwardProject
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ35D8_originalSpatialHaar_inverseProject
