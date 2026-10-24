import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPlaquetteSquareCenterV5_PY7C
import Mathlib.Tactic

/-!
# P4-Q2-PY8 — genuine diagonal spatial-plaquette gauge Ward

The original true SU(2) spatial plaquette normalized real character
χ_p(A) = 1 - E_W(Hol_p(A)) is invariant under simultaneous vertex
gauge transformations, by conjugation of the ORIGINAL four-edge
holonomy. Therefore its square is a continuous gauge-invariant
weight on the unchanged spatial Haar probability.

Apply the same real vertex-gauge change of variables already used
by PT to the ORIGINAL square of one temporal crossing plaquette
energy at any actual link e. This proves that the χ_p²-weighted
single-link crossing-square Haar pairing is independent of its
physical right boundary.

Neither the interacting two original Wilson posteriors, the full
spatial Wilson plaquette action, nor any Gauss-law source is changed.
No Dobrushin replacement, new axiom, sorry/admit, rank or fifth
coefficient nonzero assumption.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PY8_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PY8_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PY8_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PY8_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PY8_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section OriginalDiagonalPlaquetteGaugeWard
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "Gauge" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "χ" => p4Q2PV_originalPlaquetteRealCharacter H

/-- The genuine normalized real trace of ANY true spatial SU(2)
plaquette is invariant under original spatial vertex-gauge
transformations, by conjugacy of its oriented four-link holonomy. -/
theorem p4Q2PY8_originalPlaquetteChar_gaugeInvariant
    (p : Plaq) (γ : Gauge) (A : Cfg) :
    χ p (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H 2 γ A) =
      χ p A := by
  unfold p4Q2PV_originalPlaquetteRealCharacter
  rw [periodicHypercubicEvenSpatialSlicePlaquetteHolonomy_gaugeTransform]
  rw [specialUnitaryWilsonPlaquetteEnergy_conjInvariant]

/-- The original χ_p² Haar weight is continuous and exactly gauge
invariant; no independent or factorized Wilson posterior is used. -/
theorem p4Q2PY8_originalPlaquetteSquare_gaugeInvariant
    (p : Plaq) (γ : Gauge) (A : Cfg) :
    (χ p (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H 2 γ A))^2 =
      (χ p A)^2 := by
  rw [p4Q2PY8_originalPlaquetteChar_gaugeInvariant H p γ A]

/-- Genuine original spatial Haar pairing of χ_p² with the
SQUARE of one temporal SU(2) Wilson crossing plaquette energy
is exactly independent of the selected true right boundary. -/
theorem p4Q2PY8_originalPlaquetteSquare_temporalLinkSquareHaar_invariant
    (p : Plaq) (e : Link) (B : Cfg) :
    (∫ A : Cfg, (χ p A)^2 * (E ((A e)⁻¹ * B e))^2 ∂haar) =
      (∫ A : Cfg, (χ p A)^2 * (E ((A e)⁻¹))^2 ∂haar) := by
  let γ : Gauge := fun v => if v = e.1 then B e else 1
  have hsrc : γ e.1 = B e := by simp [γ]
  have htar : γ (periodicHypercubicEvenSpatialSliceShift H e.1 e.2) = 1 := by
    simp [γ, p4Q2PL_originalSpatialLink_target_ne_source H e]
  let T : Cfg → Cfg :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H 2 γ
  have hPres : MeasurePreserving T haar haar :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaar_measurePreserving H 2 γ
  have hRel (A : Cfg) :
      ((T A e)⁻¹ * B e) = (A e)⁻¹ := by
    change
      ((γ e.1 * A e *
          (γ (periodicHypercubicEvenSpatialSliceShift H e.1 e.2))⁻¹)⁻¹ *
          B e) = (A e)⁻¹
    rw [hsrc, htar]
    group
  let f : Cfg → ℝ := fun A => (χ p A)^2 * (E ((A e)⁻¹ * B e))^2
  let g : Cfg → ℝ := fun A => (χ p A)^2 * (E ((A e)⁻¹))^2
  have hChi : Continuous (fun A : Cfg => χ p A) :=
    p4Q2PV_originalPlaquetteRealCharacter_continuous H p
  have hE : Continuous (fun A : Cfg => E ((A e)⁻¹ * B e)) :=
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp
      ((continuous_apply e).inv.mul continuous_const)
  have hf : AEStronglyMeasurable f haar :=
    ((hChi.pow 2).mul (hE.pow 2)).measurable.aestronglyMeasurable
  have hPoint (A : Cfg) : f (T A) = g A := by
    change (χ p (T A))^2 * (E ((T A e)⁻¹ * B e))^2 =
      (χ p A)^2 * (E ((A e)⁻¹))^2
    rw [p4Q2PY8_originalPlaquetteSquare_gaugeInvariant H p γ A, hRel A]
  have hmap : Measure.map T haar = haar := hPres.map_eq
  have hfm : AEStronglyMeasurable f (Measure.map T haar) := by
    rw [hmap]
    exact hf
  calc
    (∫ A : Cfg, (χ p A)^2 * (E ((A e)⁻¹ * B e))^2 ∂haar) =
        ∫ A : Cfg, f A ∂haar := rfl
    _ = ∫ A : Cfg, f A ∂Measure.map T haar := by rw [hmap]
    _ = ∫ A : Cfg, f (T A) ∂haar :=
      MeasureTheory.integral_map hPres.measurable.aemeasurable hfm
    _ = ∫ A : Cfg, g A ∂haar := by
      apply integral_congr_ae
      filter_upwards with A
      exact hPoint A
    _ = (∫ A : Cfg, (χ p A)^2 * (E ((A e)⁻¹))^2 ∂haar) := rfl

end OriginalDiagonalPlaquetteGaugeWard
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY8_originalPlaquetteChar_gaugeInvariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY8_originalPlaquetteSquare_gaugeInvariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY8_originalPlaquetteSquare_temporalLinkSquareHaar_invariant
