import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalTemporalCharacterTransmissionV5_PZ37ABN
import MGAP4D.MathlibAnalytic.NormalizedCompactHaarInversion
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ABN2 — exact original one-link temporal character eigenlaw

The genuine SU(2) matrix identity g^(-1)+g=Tr(g) I yields the original
normalized-character identity
  chi(g^(-1)a) + chi(ga) = 2 chi(g) chi(a).
Inversion preserves the original compact Haar and the actual Wilson factor
k_b(g)=exp(-b E_W(g)). Integrating the identity therefore proves
  integral k_b(g) chi(g^(-1)a) dHaar(g) = N_b chi(a).
After division by the genuine positive mass Z_b, this is the exact
one-link convolution eigenlaw with ABN's proved coefficient r_b=N_b/Z_b.

Its actual transferred character has zero Haar mean and exact squared
Haar moment r_b^2/4. ABN's explicit coefficient floor supplies a positive
common lower moment on every prescribed 0<b0<=b<=B interval.

No abstract eigenvalue, Schur/Peter-Weyl assumption, posterior replacement,
or finite-group Haar substitution is used. This concerns the original
one-link temporal convolution. It does not assert a four-link product
eigenlaw, a posterior/Gauss-law full-source overlap floor, or mass gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Mat" => Matrix (Fin 2) (Fin 2) ℂ
local notation "μ" => normalizedCompactHaar G
local notation "χ" => p4Q2PZ35C_originalOneLinkCharacter
local notation "k" => specialUnitaryWilsonBoltzmannCentralFunction 2

local instance p4Q2PZ37ABN2_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ABN2_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ABN2_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ABN2_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ABN2_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ABN2_probability : IsProbabilityMeasure μ :=
  normalizedCompactHaar_isProbabilityMeasure G

namespace GroundStatePosteriorJoint

private theorem p4Q2PZ37ABN2_character_continuous : Continuous χ :=
  continuous_const.sub (continuous_specialUnitaryWilsonPlaquetteEnergy 2)

private theorem p4Q2PZ37ABN2_temporalFactor_continuous (b : ℝ) :
    Continuous (k b) := by
  unfold specialUnitaryWilsonBoltzmannCentralFunction
  exact Real.continuous_exp.comp
    (continuous_const.mul (continuous_specialUnitaryWilsonPlaquetteEnergy 2))

private theorem p4Q2PZ37ABN2_temporalFactor_inv (b : ℝ) (g : G) :
    k b (g⁻¹) = k b g := by
  unfold specialUnitaryWilsonBoltzmannCentralFunction
  rw [specialUnitaryWilsonPlaquetteEnergy_inv]

/-- The literal SU(2) matrix inverse plus the matrix itself is its trace
times the identity. Determinant one and the 2x2 adjugate suffice. -/
theorem p4Q2PZ37ABN2_originalSU2_inverse_add (g : G) :
    (((g⁻¹ : G) : Mat)) + (g : Mat) =
      Matrix.trace (g : Mat) • (1 : Mat) := by
  have hdet : Matrix.det (g : Mat) = 1 :=
    (Matrix.mem_specialUnitaryGroup_iff.mp g.property).2
  have hInv : (((g⁻¹ : G) : Mat)) = (g : Mat).adjugate := by
    rw [p4Q2PZ35D_groupInverse_coe, Matrix.inv_def, hdet,
      Ring.inverse_one, one_smul]
  rw [hInv, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.trace_fin_two, add_comm]
  · simp
  · simp
  · simp [Matrix.trace_fin_two]

/-- Pointwise original normalized SU(2) character identity. The real
character is transported through the already proved genuine real trace. -/
theorem p4Q2PZ37ABN2_originalCharacter_inverse_product_sum (g a : G) :
    χ (g⁻¹ * a) + χ (g * a) = 2 * χ g * χ a := by
  have hTrace :
      Matrix.trace (((g⁻¹ * a : G) : Mat)) +
        Matrix.trace (((g * a : G) : Mat)) =
      Matrix.trace (g : Mat) * Matrix.trace (a : Mat) := by
    have h := congrArg (fun X : Mat => Matrix.trace (X * (a : Mat)))
      (p4Q2PZ37ABN2_originalSU2_inverse_add g)
    change Matrix.trace ((((g⁻¹ : G) : Mat) * (a : Mat))) +
        Matrix.trace ((g : Mat) * (a : Mat)) = _
    simpa only [add_mul, Matrix.smul_mul, one_mul,
      Matrix.trace_add, Matrix.trace_smul, smul_eq_mul] using h
  have hComplex :
      ((χ (g⁻¹ * a) : ℝ) : ℂ) + ((χ (g * a) : ℝ) : ℂ) =
        2 * ((χ g : ℝ) : ℂ) * ((χ a : ℝ) : ℂ) := by
    simp_rw [p4Q2PZ35D2_originalCharacter_complex_coe]
    rw [← add_div, hTrace]
    ring
  exact_mod_cast hComplex

/-- The original one-link temporal Wilson convolution acts on the original
character by its actual unnormalized Haar moment. No spectral premise. -/
theorem p4Q2PZ37ABN2_originalTemporalCharacter_convolution
    (b : ℝ) (a : G) :
    (∫ g : G, k b g * χ (g⁻¹ * a) ∂μ) =
      p4Q2PZ37ABN_originalTemporalWilsonCharacterMoment b * χ a := by
  let F : G → ℝ := fun g => k b g * χ (g⁻¹ * a)
  let R : G → ℝ := fun g => k b g * χ (g * a)
  have hF : Continuous F :=
    (p4Q2PZ37ABN2_temporalFactor_continuous b).mul
      (p4Q2PZ37ABN2_character_continuous.comp
        (continuous_id.inv.mul continuous_const))
  have hR : Continuous R :=
    (p4Q2PZ37ABN2_temporalFactor_continuous b).mul
      (p4Q2PZ37ABN2_character_continuous.comp
        (continuous_id.mul continuous_const))
  have hFI : Integrable F μ :=
    hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hRI : Integrable R μ :=
    hR.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hReflection : (∫ g : G, F g ∂μ) = ∫ g : G, R g ∂μ := by
    have hmp := normalizedCompactHaar_measurePreserving_inv G
    have hMap :
        (∫ g : G, F g ∂Measure.map Inv.inv μ) =
          ∫ g : G, F (g⁻¹) ∂μ :=
      integral_map_of_stronglyMeasurable hmp.measurable hF.stronglyMeasurable
    rw [hmp.map_eq] at hMap
    simpa only [F, R, p4Q2PZ37ABN2_temporalFactor_inv, inv_inv] using hMap
  have hSum :
      (∫ g : G, F g ∂μ) + (∫ g : G, R g ∂μ) =
        2 * p4Q2PZ37ABN_originalTemporalWilsonCharacterMoment b * χ a := by
    calc
      (∫ g : G, F g ∂μ) + (∫ g : G, R g ∂μ) =
          ∫ g : G, (F g + R g) ∂μ := (integral_add hFI hRI).symm
      _ = ∫ g : G, (k b g * χ g) * (2 * χ a) ∂μ := by
        apply integral_congr_ae
        filter_upwards with g
        dsimp [F, R]
        rw [← mul_add, p4Q2PZ37ABN2_originalCharacter_inverse_product_sum]
        ring
      _ = (∫ g : G, k b g * χ g ∂μ) * (2 * χ a) :=
        integral_mul_const _ _
      _ = 2 * p4Q2PZ37ABN_originalTemporalWilsonCharacterMoment b * χ a := by
        unfold p4Q2PZ37ABN_originalTemporalWilsonCharacterMoment
        ring
  rw [← hReflection] at hSum
  change (∫ g : G, F g ∂μ) = _
  linarith

/-- The actual one-link transferred character: integrate the genuine
temporal Wilson factor against original Haar, divide by its actual mass. -/
noncomputable def p4Q2PZ37ABN2_originalTemporalCharacterTransfer
    (b : ℝ) (a : G) : ℝ :=
  (∫ g : G, k b g * χ (g⁻¹ * a) ∂μ) /
    p4Q2PZ37ABN_originalTemporalWilsonMass b

/-- Exact normalized eigenlaw, with the independently proved original
coefficient r_b. The genuine one-link Haar mass normalization Z_b remains
explicit; Z_b is not the full physical transfer norm t. -/
theorem p4Q2PZ37ABN2_originalTemporalCharacterTransfer_eq_coefficient_mul
    (b : ℝ) (a : G) :
    p4Q2PZ37ABN2_originalTemporalCharacterTransfer b a =
      p4Q2PZ37ABN_originalTemporalWilsonCoefficient b * χ a := by
  unfold p4Q2PZ37ABN2_originalTemporalCharacterTransfer
  rw [p4Q2PZ37ABN2_originalTemporalCharacter_convolution]
  unfold p4Q2PZ37ABN_originalTemporalWilsonCoefficient
  ring

/-- The actual transferred character has exactly zero original Haar mean. -/
theorem p4Q2PZ37ABN2_originalTemporalCharacterTransfer_haar_mean_zero
    (b : ℝ) :
    (∫ a : G, p4Q2PZ37ABN2_originalTemporalCharacterTransfer b a ∂μ) = 0 := by
  simp_rw [p4Q2PZ37ABN2_originalTemporalCharacterTransfer_eq_coefficient_mul]
  rw [integral_const_mul, p4Q2PZ35D4_originalOneLinkHaar_characterZero, mul_zero]

/-- Its exact Haar second moment is r_b^2/4. By the preceding mean-zero
theorem, this is also its actual centered Haar variance. -/
theorem p4Q2PZ37ABN2_originalTemporalCharacterTransfer_haar_secondMoment
    (b : ℝ) :
    (∫ a : G, (p4Q2PZ37ABN2_originalTemporalCharacterTransfer b a)^2 ∂μ) =
      (p4Q2PZ37ABN_originalTemporalWilsonCoefficient b)^2 / 4 := by
  calc
    (∫ a : G, (p4Q2PZ37ABN2_originalTemporalCharacterTransfer b a)^2 ∂μ) =
        ∫ a : G, (p4Q2PZ37ABN_originalTemporalWilsonCoefficient b)^2 *
          (χ a)^2 ∂μ := by
      apply integral_congr_ae
      filter_upwards with a
      rw [p4Q2PZ37ABN2_originalTemporalCharacterTransfer_eq_coefficient_mul]
      ring
    _ = (p4Q2PZ37ABN_originalTemporalWilsonCoefficient b)^2 * (1 / 4 : ℝ) := by
      rw [integral_const_mul, p4Q2PZ37ABN_originalTemporalCharacter_haar_secondMoment]
    _ = (p4Q2PZ37ABN_originalTemporalWilsonCoefficient b)^2 / 4 := by ring

/-- A true original temporal transferred-mode Haar-variance floor, common
on the whole prescribed positive coupling interval. No H-dependent input
or assumed character eigenlaw occurs in this conclusion. -/
theorem p4Q2PZ37ABN2_originalTemporalCharacterTransfer_positive_interval
    (b0 B b : ℝ) (hb0 : 0 < b0) (hLower : b0 ≤ b) (hUpper : b ≤ B) :
    0 < (b0 * Real.exp (-2 * B) / 4)^2 / 4 ∧
      (b0 * Real.exp (-2 * B) / 4)^2 / 4 ≤
        ∫ a : G, (p4Q2PZ37ABN2_originalTemporalCharacterTransfer b a)^2 ∂μ := by
  have hFloor : 0 < b0 * Real.exp (-2 * B) / 4 := by positivity
  have hCoefficient :=
    p4Q2PZ37ABN_originalTemporalWilsonCoefficient_uniform_lower
      b0 B b hb0 hLower hUpper
  have hSquare := mul_le_mul hCoefficient hCoefficient
    hFloor.le (hFloor.le.trans hCoefficient)
  refine ⟨by positivity, ?_⟩
  rw [p4Q2PZ37ABN2_originalTemporalCharacterTransfer_haar_secondMoment]
  nlinarith

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABN2_originalSU2_inverse_add
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABN2_originalCharacter_inverse_product_sum
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABN2_originalTemporalCharacter_convolution
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABN2_originalTemporalCharacterTransfer_eq_coefficient_mul
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABN2_originalTemporalCharacterTransfer_haar_mean_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABN2_originalTemporalCharacterTransfer_haar_secondMoment
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABN2_originalTemporalCharacterTransfer_positive_interval
