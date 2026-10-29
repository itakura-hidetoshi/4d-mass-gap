import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalTemporalCharacterEigenlawV5_PZ37ABN2
import MGAP4D.MathlibAnalytic.SpecialUnitaryNormalizedTraceCyclic
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ABO — original one-link convolution in either plaquette orientation

Translate the exact ABN2 one-link eigenlaw by genuine SU(2) Haar invariance.
For the actual Wilson factor k_b and original character chi=1-E_W, obtain
  integral k_b(x^(-1)y) chi(a x c) dHaar(x) = N_b chi(a y c),
  integral k_b(x^(-1)y) chi(a x^(-1) c) dHaar(x)
    = N_b chi(a y^(-1) c).
The surrounding words a,c and target y are arbitrary actual SU(2) elements.
The mass of the SAME relative Wilson factor is exactly the genuine Z_b.

These are all-real-coupling identities for the unchanged original temporal
factor and normalized compact Haar. Trace cyclicity and inversion invariance
are proved for the original Wilson character. No commutativity of SU(2),
posterior independence, artificial Haar law, or spectral premise is used.
Z_b remains the one-link Haar mass, not the full physical transfer norm t.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "μ" => normalizedCompactHaar G
local notation "χ" => p4Q2PZ35C_originalOneLinkCharacter
local notation "k" => specialUnitaryWilsonBoltzmannCentralFunction 2

local instance p4Q2PZ37ABO_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ABO_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ABO_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ABO_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ABO_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ABO_probability : IsProbabilityMeasure μ :=
  normalizedCompactHaar_isProbabilityMeasure G

namespace GroundStatePosteriorJoint

private theorem p4Q2PZ37ABO_character_continuous : Continuous χ :=
  continuous_const.sub (continuous_specialUnitaryWilsonPlaquetteEnergy 2)

private theorem p4Q2PZ37ABO_temporalFactor_continuous (b : ℝ) :
    Continuous (k b) := by
  unfold specialUnitaryWilsonBoltzmannCentralFunction
  exact Real.continuous_exp.comp
    (continuous_const.mul (continuous_specialUnitaryWilsonPlaquetteEnergy 2))

private theorem p4Q2PZ37ABO_temporalFactor_inv (b : ℝ) (g : G) :
    k b (g⁻¹) = k b g := by
  unfold specialUnitaryWilsonBoltzmannCentralFunction
  rw [specialUnitaryWilsonPlaquetteEnergy_inv]

private theorem p4Q2PZ37ABO_character_inv (g : G) : χ (g⁻¹) = χ g := by
  unfold p4Q2PZ35C_originalOneLinkCharacter
  rw [specialUnitaryWilsonPlaquetteEnergy_inv]

private theorem p4Q2PZ37ABO_character_cycle (g h : G) :
    χ (g * h) = χ (h * g) := by
  simp only [p4Q2PZ35C_originalOneLinkCharacter,
    specialUnitaryWilsonPlaquetteEnergy_eq,
    normalizedSpecialUnitaryRealTrace_mul_cycle g h]

/-- The original relative one-link temporal Wilson factor has its exact
genuine Haar mass Z_b at every actual target group element. -/
theorem p4Q2PZ37ABO_originalOneLink_mass (b : ℝ) (y : G) :
    (∫ x : G, k b (x⁻¹ * y) ∂μ) =
      p4Q2PZ37ABN_originalTemporalWilsonMass b := by
  let F : G → ℝ := fun x => k b (x⁻¹ * y)
  have hF : Continuous F :=
    (p4Q2PZ37ABO_temporalFactor_continuous b).comp
      (continuous_id.inv.mul continuous_const)
  have hPoint (g : G) : F (y * g) = k b g := by
    dsimp [F]
    rw [show (y * g)⁻¹ * y = g⁻¹ by group]
    exact p4Q2PZ37ABO_temporalFactor_inv b g
  calc
    (∫ x : G, k b (x⁻¹ * y) ∂μ) = ∫ g : G, F (y * g) ∂μ :=
      (p4Q2PZ35C_originalSU2Haar_integral_left_translate F hF y).symm
    _ = ∫ g : G, k b g ∂μ := by
      apply integral_congr_ae
      filter_upwards with g
      exact hPoint g
    _ = p4Q2PZ37ABN_originalTemporalWilsonMass b := rfl

/-- Integrate an inverse-oriented occurrence of a true plaquette link,
retaining both arbitrary surrounding SU(2) words and the actual kernel. -/
theorem p4Q2PZ37ABO_originalOneLink_inverse (b : ℝ) (a y c : G) :
    (∫ x : G, k b (x⁻¹ * y) * χ (a * x⁻¹ * c) ∂μ) =
      p4Q2PZ37ABN_originalTemporalWilsonCharacterMoment b * χ (a * y⁻¹ * c) := by
  let F : G → ℝ := fun x => k b (x⁻¹ * y) * χ (a * x⁻¹ * c)
  have hF : Continuous F :=
    ((p4Q2PZ37ABO_temporalFactor_continuous b).comp
      (continuous_id.inv.mul continuous_const)).mul
        (p4Q2PZ37ABO_character_continuous.comp
          ((continuous_const.mul continuous_id.inv).mul continuous_const))
  have hCharacter (g : G) :
      χ (a * (y * g)⁻¹ * c) = χ (g⁻¹ * (y⁻¹ * c * a)) := by
    calc
      χ (a * (y * g)⁻¹ * c) = χ (a * ((y * g)⁻¹ * c)) := by
        rw [mul_assoc]
      _ = χ (((y * g)⁻¹ * c) * a) :=
        p4Q2PZ37ABO_character_cycle a ((y * g)⁻¹ * c)
      _ = χ (g⁻¹ * (y⁻¹ * c * a)) := by
        congr 1
        group
  have hPoint (g : G) :
      F (y * g) = k b g * χ (g⁻¹ * (y⁻¹ * c * a)) := by
    dsimp [F]
    rw [show (y * g)⁻¹ * y = g⁻¹ by group,
      p4Q2PZ37ABO_temporalFactor_inv, hCharacter]
  calc
    (∫ x : G, k b (x⁻¹ * y) * χ (a * x⁻¹ * c) ∂μ) =
        ∫ g : G, F (y * g) ∂μ :=
      (p4Q2PZ35C_originalSU2Haar_integral_left_translate F hF y).symm
    _ = ∫ g : G, k b g * χ (g⁻¹ * (y⁻¹ * c * a)) ∂μ := by
      apply integral_congr_ae
      filter_upwards with g
      exact hPoint g
    _ = p4Q2PZ37ABN_originalTemporalWilsonCharacterMoment b *
        χ (y⁻¹ * c * a) :=
      p4Q2PZ37ABN2_originalTemporalCharacter_convolution b (y⁻¹ * c * a)
    _ = p4Q2PZ37ABN_originalTemporalWilsonCharacterMoment b *
        χ (a * y⁻¹ * c) := by
      congr 1
      simpa only [mul_assoc] using
        (p4Q2PZ37ABO_character_cycle (y⁻¹ * c) a)

/-- Integrate a forward-oriented occurrence of a true plaquette link.
Character inversion reduces this to the exact inverse-oriented identity;
the surrounding words retain their original noncommutative order. -/
theorem p4Q2PZ37ABO_originalOneLink_forward (b : ℝ) (a y c : G) :
    (∫ x : G, k b (x⁻¹ * y) * χ (a * x * c) ∂μ) =
      p4Q2PZ37ABN_originalTemporalWilsonCharacterMoment b * χ (a * y * c) := by
  have hCharacter (x : G) : χ (a * x * c) = χ (c⁻¹ * x⁻¹ * a⁻¹) := by
    calc
      χ (a * x * c) = χ ((a * x * c)⁻¹) :=
        (p4Q2PZ37ABO_character_inv (a * x * c)).symm
      _ = χ (c⁻¹ * x⁻¹ * a⁻¹) := by
        congr 1
        group
  calc
    (∫ x : G, k b (x⁻¹ * y) * χ (a * x * c) ∂μ) =
        ∫ x : G, k b (x⁻¹ * y) * χ (c⁻¹ * x⁻¹ * a⁻¹) ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [hCharacter]
    _ = p4Q2PZ37ABN_originalTemporalWilsonCharacterMoment b *
        χ (c⁻¹ * y⁻¹ * a⁻¹) :=
      p4Q2PZ37ABO_originalOneLink_inverse b c⁻¹ y a⁻¹
    _ = p4Q2PZ37ABN_originalTemporalWilsonCharacterMoment b * χ (a * y * c) := by
      rw [← hCharacter y]

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABO_originalOneLink_mass
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABO_originalOneLink_inverse
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABO_originalOneLink_forward
