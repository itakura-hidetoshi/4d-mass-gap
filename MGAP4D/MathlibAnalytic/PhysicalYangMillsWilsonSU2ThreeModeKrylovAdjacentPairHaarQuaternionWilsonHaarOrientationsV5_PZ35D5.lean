import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarQuaternionWilsonHaarContractionV5_PZ35D4
import Mathlib.Tactic

/-!
# P4-Q2-PZ35D5 — genuine SU(2) one-link Schur contractions in both orientations

The original plaquette holonomy contains two spatial links in the
forward orientation and two in the inverse orientation. This module
proves two EXACT one-link Haar contraction lemmas with arbitrary
surrounding original SU(2) group factors, using only the genuine
normalized Haar measure and PZ35D4, never a substitute measure.

These are the local contraction theorems needed to iterate Fubini on
four distinct links. The four-link product-measure Fubini theorem is
still open and is NOT asserted in this module.

No additional axioms, sorry, admit, native_decide or altered model.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Mat" => Matrix (Fin 2) (Fin 2) ℂ
local notation "χ" => p4Q2PZ35C_originalOneLinkCharacter
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "μ" => normalizedCompactHaar G

local instance p4Q2PZ35D5_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance p4Q2PZ35D5_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2

local instance p4Q2PZ35D5_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2

local instance p4Q2PZ35D5_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2

local instance p4Q2PZ35D5_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

local instance p4Q2PZ35D5_probability : IsProbabilityMeasure μ :=
  normalizedCompactHaar_isProbabilityMeasure G

/-- Original normalized SU(2) Wilson character is cyclic for two
factors, using genuine matrix trace, not a class-function axiom. -/
theorem p4Q2PZ35D5_originalCharacter_mul_comm (a b : G) :
    χ (a * b) = χ (b * a) := by
  have hc :
      ((χ (a * b) : ℝ) : ℂ) = ((χ (b * a) : ℝ) : ℂ) := by
    rw [p4Q2PZ35D2_originalCharacter_complex_coe,
      p4Q2PZ35D2_originalCharacter_complex_coe]
    change Matrix.trace ((a : Mat) * (b : Mat)) / 2 =
      Matrix.trace ((b : Mat) * (a : Mat)) / 2
    rw [Matrix.trace_mul_comm]
  exact_mod_cast hc

/-- Original SU(2) Wilson character is invariant under group inversion. -/
theorem p4Q2PZ35D5_originalCharacter_inv (u : G) :
    χ u⁻¹ = χ u := by
  have hc :
      ((χ u⁻¹ : ℝ) : ℂ) = ((χ u : ℝ) : ℂ) := by
    rw [p4Q2PZ35D2_originalCharacter_complex_coe,
      p4Q2PZ35D2_originalCharacter_complex_coe,
      p4Q2PZ35D_trace_inverse_eq u]
  exact_mod_cast hc

/-- Original Wilson energy is central on SU(2), proved from
two-factor trace cyclicity. -/
theorem p4Q2PZ35D5_originalEnergy_conjugate (c x : G) :
    E (c⁻¹ * x * c) = E x := by
  have hχ : χ (c⁻¹ * x * c) = χ x := by
    calc
      χ (c⁻¹ * x * c) = χ ((c⁻¹ * x) * c) := rfl
      _ = χ (c * (c⁻¹ * x)) :=
        p4Q2PZ35D5_originalCharacter_mul_comm (c⁻¹ * x) c
      _ = χ x := by
        have hg : c * (c⁻¹ * x) = x := by group
        rw [hg]
  unfold p4Q2PZ35C_originalOneLinkCharacter at hχ
  linarith

/-- Genuine normalized compact SU(2) Haar is right-translation
invariant for continuous real tests, derived from actual bi-Haar. -/
theorem p4Q2PZ35D5_originalSU2Haar_integral_right_translate
    (f : G → ℝ) (hf : Continuous f) (c : G) :
    (∫ u : G, f (u * c) ∂μ) = (∫ u : G, f u ∂μ) := by
  have hp : MeasurePreserving (fun u : G => u * c) μ μ := by
    simpa only [one_mul] using
      (normalizedCompactHaar_measurePreserving_mul_left_right G (1 : G) c)
  have hMeas :
      AEStronglyMeasurable f (Measure.map (fun u : G => u * c) μ) := by
    rw [hp.map_eq]
    exact hf.measurable.aestronglyMeasurable
  calc
    (∫ u : G, f (u * c) ∂μ) =
        (∫ u : G, f u ∂Measure.map (fun u : G => u * c) μ) :=
      (MeasureTheory.integral_map hp.measurable.aemeasurable hMeas).symm
    _ = (∫ u : G, f u ∂μ) := by
      rw [hp.map_eq]

/-- Original SU(2) Wilson one-link contraction in the FORWARD
orientation with any actual SU(2) factor to the right. -/
theorem p4Q2PZ35D5_originalOneLinkHaar_forward
    (b c : G) :
    (∫ u : G, χ (u * c) * E (u⁻¹ * b) ∂μ) =
      -(1 / 4 : ℝ) * χ (b * c) := by
  let f : G → ℝ := fun v => χ v * E (v⁻¹ * (b * c))
  have hc : Continuous χ :=
    continuous_const.sub (continuous_specialUnitaryWilsonPlaquetteEnergy 2)
  have hfc : Continuous f :=
    hc.mul ((continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp
      (continuous_id.inv.mul continuous_const))
  have hTranslate (u : G) :
      f (u * c) = χ (u * c) * E (u⁻¹ * b) := by
    dsimp [f]
    have hg : (u * c)⁻¹ * (b * c) = c⁻¹ * (u⁻¹ * b) * c := by
      group
    rw [hg, p4Q2PZ35D5_originalEnergy_conjugate]
  calc
    (∫ u : G, χ (u * c) * E (u⁻¹ * b) ∂μ) =
        (∫ u : G, f (u * c) ∂μ) := by
      apply integral_congr_ae
      filter_upwards with u
      exact (hTranslate u).symm
    _ = (∫ v : G, f v ∂μ) :=
      p4Q2PZ35D5_originalSU2Haar_integral_right_translate f hfc c
    _ = -(1 / 4 : ℝ) * χ (b * c) := by
      exact p4Q2PZ35D4_originalOneLinkHaar_characterEnergy (b * c)

/-- Original SU(2) Wilson one-link contraction in the INVERSE
orientation. The target orientation is exactly B⁻¹*c. -/
theorem p4Q2PZ35D5_originalOneLinkHaar_inverse
    (b c : G) :
    (∫ u : G, χ (u⁻¹ * c) * E (u⁻¹ * b) ∂μ) =
      -(1 / 4 : ℝ) * χ (b⁻¹ * c) := by
  have hPoint (u : G) : χ (u⁻¹ * c) = χ (u * c⁻¹) := by
    calc
      χ (u⁻¹ * c) = χ ((u⁻¹ * c)⁻¹) :=
        (p4Q2PZ35D5_originalCharacter_inv (u⁻¹ * c)).symm
      _ = χ (c⁻¹ * u) := by
        rw [mul_inv_rev, inv_inv]
      _ = χ (u * c⁻¹) :=
        p4Q2PZ35D5_originalCharacter_mul_comm c⁻¹ u
  have hOut : χ (b * c⁻¹) = χ (b⁻¹ * c) := by
    calc
      χ (b * c⁻¹) = χ ((b * c⁻¹)⁻¹) :=
        (p4Q2PZ35D5_originalCharacter_inv (b * c⁻¹)).symm
      _ = χ (c * b⁻¹) := by
        rw [mul_inv_rev, inv_inv]
      _ = χ (b⁻¹ * c) :=
        p4Q2PZ35D5_originalCharacter_mul_comm c b⁻¹
  calc
    (∫ u : G, χ (u⁻¹ * c) * E (u⁻¹ * b) ∂μ) =
        (∫ u : G, χ (u * c⁻¹) * E (u⁻¹ * b) ∂μ) := by
      apply integral_congr_ae
      filter_upwards with u
      rw [hPoint]
    _ = -(1 / 4 : ℝ) * χ (b * c⁻¹) :=
      p4Q2PZ35D5_originalOneLinkHaar_forward b c⁻¹
    _ = -(1 / 4 : ℝ) * χ (b⁻¹ * c) := by rw [hOut]

end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ35D5_originalCharacter_mul_comm
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ35D5_originalCharacter_inv
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ35D5_originalEnergy_conjugate
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ35D5_originalSU2Haar_integral_right_translate
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ35D5_originalOneLinkHaar_forward
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ35D5_originalOneLinkHaar_inverse
