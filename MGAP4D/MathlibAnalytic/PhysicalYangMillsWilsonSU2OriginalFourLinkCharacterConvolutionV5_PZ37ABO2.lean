import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalOneLinkCharacterConvolutionV5_PZ37ABO
import MGAP4D.MathlibAnalytic.HaarFinFourCyclicPlaquetteL2
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ABO2 — the actual four-link temporal Wilson character eigenlaw

On the genuine four-fold normalized compact SU(2) Haar product, use the
literal temporal kernel product
  product_i k_b(x_i^(-1) y_i)
and the original cyclic plaquette character
  chi(x_2^(-1) x_3^(-1) x_0 x_1).

The existing Haar coordinate transport gives four ordinary integrals.
ABO's two original one-link orientation identities evaluate each integral,
without changing the noncommutative word or assuming an eigenvalue law.
The unnormalized character coefficient is N_b^4, the true kernel mass is
Z_b^4, and the normalized character coefficient is r_b^4.

This is an identity for the original four temporal factors. Normalization
uses only their genuine product Haar mass Z_b^4, not the full physical
transfer norm t. Spatial interactions, remote marginal weights, Perron
factors, the signed interacting posterior contrast, and full-source
plaquette cancellation are not removed or controlled by this identity.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "X" => Fin 4 → G
local notation "P" => ((G × G) × G) × G
local notation "μ" => normalizedCompactHaar G
local notation "ν" => Measure.pi (fun _ : Fin 4 => μ)
local notation "χ" => p4Q2PZ35C_originalOneLinkCharacter
local notation "k" => specialUnitaryWilsonBoltzmannCentralFunction 2

local instance p4Q2PZ37ABO2_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ABO2_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ABO2_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ABO2_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ABO2_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ABO2_probability : IsProbabilityMeasure μ :=
  normalizedCompactHaar_isProbabilityMeasure G

namespace GroundStatePosteriorJoint

private theorem p4Q2PZ37ABO2_character_continuous : Continuous χ :=
  continuous_const.sub (continuous_specialUnitaryWilsonPlaquetteEnergy 2)

private theorem p4Q2PZ37ABO2_relative_continuous (b : ℝ) (y : G) :
    Continuous (fun x : G => k b (x⁻¹ * y)) := by
  have hk : Continuous (k b) := by
    unfold specialUnitaryWilsonBoltzmannCentralFunction
    exact Real.continuous_exp.comp
      (continuous_const.mul (continuous_specialUnitaryWilsonPlaquetteEnergy 2))
  exact hk.comp (continuous_id.inv.mul continuous_const)

private theorem p4Q2PZ37ABO2_word_eq (x : X) :
    haarFinFourCyclicPlaquetteWord x = (x 2)⁻¹ * (x 3)⁻¹ * x 0 * x 1 := by
  simp only [haarFinFourCyclicPlaquetteWord,
    haarFinFourCyclicNestedCoordinates_apply, haarCyclicPlaquetteWord, mul_assoc]

/-- The concrete existing Haar reshaping has nested order
(((x1,x0),x3),x2). Fubini therefore integrates x1 first, then x0,
then x3 and finally x2; no coordinate permutation is implicit. -/
private theorem p4Q2PZ37ABO2_integral_finFour
    (f : G → G → G → G → ℝ)
    (hf : Continuous (fun p : P => f p.1.1.2 p.1.1.1 p.2 p.1.2)) :
    (∫ x : X, f (x 0) (x 1) (x 2) (x 3) ∂ν) =
      ∫ x2 : G, ∫ x3 : G, ∫ x0 : G, ∫ x1 : G,
        f x0 x1 x2 x3 ∂μ ∂μ ∂μ ∂μ := by
  let F : P → ℝ := fun p => f p.1.1.2 p.1.1.1 p.2 p.1.2
  have hF : Continuous F := hf
  have hFI : Integrable F (((μ.prod μ).prod μ).prod μ) :=
    hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hmp := measurePreserving_haarFinFourCyclicNestedCoordinates μ
  have hMap :
      (∫ p : P, F p ∂(((μ.prod μ).prod μ).prod μ)) =
        ∫ x : X, F (haarFinFourCyclicNestedCoordinates x) ∂ν := by
    have h := integral_map_of_stronglyMeasurable
      («μ» := ν) hmp.measurable hF.stronglyMeasurable
    rw [hmp.map_eq] at h
    exact h
  calc
    (∫ x : X, f (x 0) (x 1) (x 2) (x 3) ∂ν) =
        ∫ x : X, F (haarFinFourCyclicNestedCoordinates x) ∂ν := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [haarFinFourCyclicNestedCoordinates_apply, F]
    _ = ∫ p : P, F p ∂(((μ.prod μ).prod μ).prod μ) := hMap.symm
    _ = ∫ x2 : G, ∫ q : (G × G) × G, F (q, x2) ∂((μ.prod μ).prod μ) ∂μ :=
      integral_prod_symm F hFI
    _ = ∫ x2 : G, ∫ x3 : G, ∫ q : G × G, F ((q, x3), x2) ∂(μ.prod μ) ∂μ ∂μ := by
      apply integral_congr_ae
      filter_upwards with x2
      have h3 : Continuous (fun q : (G × G) × G => F (q, x2)) :=
        hF.comp (continuous_id.prodMk continuous_const)
      exact integral_prod_symm _
        (h3.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    _ = ∫ x2 : G, ∫ x3 : G, ∫ x0 : G, ∫ x1 : G,
        f x0 x1 x2 x3 ∂μ ∂μ ∂μ ∂μ := by
      apply integral_congr_ae
      filter_upwards with x2
      apply integral_congr_ae
      filter_upwards with x3
      have h2 : Continuous (fun q : G × G => F ((q, x3), x2)) :=
        hF.comp ((continuous_id.prodMk continuous_const).prodMk continuous_const)
      exact integral_prod_symm _
        (h2.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

private theorem p4Q2PZ37ABO2_integral_middle_constant
    (c : ℝ) (f g : G → ℝ) :
    (∫ x : G, f x * (c * g x) ∂μ) = c * ∫ x : G, f x * g x ∂μ := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  ring

/-- The literal product of the original four temporal Wilson factors.
The relative argument x_i^(-1)y_i is the original Wilson-kernel orientation. -/
noncomputable def p4Q2PZ37ABO2_originalFourLinkWilsonKernel
    (b : ℝ) (x y : X) : ℝ :=
  ∏ i : Fin 4, k b ((x i)⁻¹ * y i)

/-- Exact genuine Haar mass of the actual four-factor temporal product.
This is Z_b^4, with no physical transfer-norm normalization. -/
theorem p4Q2PZ37ABO2_originalFourLinkWilsonKernel_mass
    (b : ℝ) (y : X) :
    (∫ x : X, p4Q2PZ37ABO2_originalFourLinkWilsonKernel b x y ∂ν) =
      (p4Q2PZ37ABN_originalTemporalWilsonMass b)^4 := by
  have h0 : Continuous (fun p : P => k b (p.1.1.2⁻¹ * y 0)) :=
    (p4Q2PZ37ABO2_relative_continuous b (y 0)).comp continuous_fst.fst.snd
  have h1 : Continuous (fun p : P => k b (p.1.1.1⁻¹ * y 1)) :=
    (p4Q2PZ37ABO2_relative_continuous b (y 1)).comp continuous_fst.fst.fst
  have h2 : Continuous (fun p : P => k b (p.2⁻¹ * y 2)) :=
    (p4Q2PZ37ABO2_relative_continuous b (y 2)).comp continuous_snd
  have h3 : Continuous (fun p : P => k b (p.1.2⁻¹ * y 3)) :=
    (p4Q2PZ37ABO2_relative_continuous b (y 3)).comp continuous_fst.snd
  unfold p4Q2PZ37ABO2_originalFourLinkWilsonKernel
  simp_rw [Fin.prod_univ_four]
  rw [p4Q2PZ37ABO2_integral_finFour
    (fun x0 x1 x2 x3 => k b (x0⁻¹ * y 0) * k b (x1⁻¹ * y 1) *
      k b (x2⁻¹ * y 2) * k b (x3⁻¹ * y 3))
    (((h0.mul h1).mul h2).mul h3)]
  simp only [integral_mul_const, integral_const_mul, p4Q2PZ37ABO_originalOneLink_mass]
  ring

/-- Dividing by the actual product Haar mass gives mass one, i.e. the
constant mode of this genuine normalized four-link convolution is fixed. -/
theorem p4Q2PZ37ABO2_originalFourLinkWilsonKernel_normalized_mass
    (b : ℝ) (y : X) :
    (∫ x : X, p4Q2PZ37ABO2_originalFourLinkWilsonKernel b x y /
      (p4Q2PZ37ABN_originalTemporalWilsonMass b)^4 ∂ν) = 1 := by
  rw [integral_div, p4Q2PZ37ABO2_originalFourLinkWilsonKernel_mass]
  exact div_self (pow_ne_zero 4 (p4Q2PZ37ABN_originalTemporalWilsonMass_pos b).ne')

/-- Four integrations of the original one-link laws give the actual
unnormalized cyclic plaquette coefficient N_b^4. Neither the four-link
eigenlaw nor a tensor spectral theorem is a premise. -/
theorem p4Q2PZ37ABO2_originalFourLinkCharacter_convolution
    (b : ℝ) (y : X) :
    (∫ x : X, p4Q2PZ37ABO2_originalFourLinkWilsonKernel b x y *
      χ (haarFinFourCyclicPlaquetteWord x) ∂ν) =
      (p4Q2PZ37ABN_originalTemporalWilsonCharacterMoment b)^4 *
        χ (haarFinFourCyclicPlaquetteWord y) := by
  let n : ℝ := p4Q2PZ37ABN_originalTemporalWilsonCharacterMoment b
  have hOne1 (x0 x2 x3 : G) :
      (∫ x1 : G, k b (x1⁻¹ * y 1) * χ (x2⁻¹ * x3⁻¹ * x0 * x1) ∂μ) =
        n * χ (x2⁻¹ * x3⁻¹ * x0 * y 1) := by
    simpa only [mul_one] using
      (p4Q2PZ37ABO_originalOneLink_forward b (x2⁻¹ * x3⁻¹ * x0) (y 1) 1)
  have hOne0 (x2 x3 : G) :
      (∫ x0 : G, k b (x0⁻¹ * y 0) * χ (x2⁻¹ * x3⁻¹ * x0 * y 1) ∂μ) =
        n * χ (x2⁻¹ * x3⁻¹ * y 0 * y 1) :=
    p4Q2PZ37ABO_originalOneLink_forward b (x2⁻¹ * x3⁻¹) (y 0) (y 1)
  have hOne3 (x2 : G) :
      (∫ x3 : G, k b (x3⁻¹ * y 3) * χ (x2⁻¹ * x3⁻¹ * y 0 * y 1) ∂μ) =
        n * χ (x2⁻¹ * (y 3)⁻¹ * y 0 * y 1) := by
    simpa only [mul_assoc] using
      (p4Q2PZ37ABO_originalOneLink_inverse b x2⁻¹ (y 3) (y 0 * y 1))
  have hOne2 :
      (∫ x2 : G, k b (x2⁻¹ * y 2) * χ (x2⁻¹ * (y 3)⁻¹ * y 0 * y 1) ∂μ) =
        n * χ ((y 2)⁻¹ * (y 3)⁻¹ * y 0 * y 1) := by
    simpa only [one_mul, mul_assoc] using
      (p4Q2PZ37ABO_originalOneLink_inverse b 1 (y 2) ((y 3)⁻¹ * y 0 * y 1))
  have h0 : Continuous (fun p : P => k b (p.1.1.2⁻¹ * y 0)) :=
    (p4Q2PZ37ABO2_relative_continuous b (y 0)).comp continuous_fst.fst.snd
  have h1 : Continuous (fun p : P => k b (p.1.1.1⁻¹ * y 1)) :=
    (p4Q2PZ37ABO2_relative_continuous b (y 1)).comp continuous_fst.fst.fst
  have h2 : Continuous (fun p : P => k b (p.2⁻¹ * y 2)) :=
    (p4Q2PZ37ABO2_relative_continuous b (y 2)).comp continuous_snd
  have h3 : Continuous (fun p : P => k b (p.1.2⁻¹ * y 3)) :=
    (p4Q2PZ37ABO2_relative_continuous b (y 3)).comp continuous_fst.snd
  have hWord : Continuous
      (fun p : P => p.2⁻¹ * p.1.2⁻¹ * p.1.1.2 * p.1.1.1) := by fun_prop
  have hChar := p4Q2PZ37ABO2_character_continuous.comp hWord
  calc
    (∫ x : X, p4Q2PZ37ABO2_originalFourLinkWilsonKernel b x y *
        χ (haarFinFourCyclicPlaquetteWord x) ∂ν) =
        ∫ x : X, k b ((x 2)⁻¹ * y 2) *
          (k b ((x 3)⁻¹ * y 3) * (k b ((x 0)⁻¹ * y 0) *
            (k b ((x 1)⁻¹ * y 1) * χ ((x 2)⁻¹ * (x 3)⁻¹ * x 0 * x 1)))) ∂ν := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [p4Q2PZ37ABO2_originalFourLinkWilsonKernel, Fin.prod_univ_four,
        p4Q2PZ37ABO2_word_eq]
      ring
    _ = ∫ x2 : G, ∫ x3 : G, ∫ x0 : G, ∫ x1 : G,
        k b (x2⁻¹ * y 2) * (k b (x3⁻¹ * y 3) * (k b (x0⁻¹ * y 0) *
          (k b (x1⁻¹ * y 1) * χ (x2⁻¹ * x3⁻¹ * x0 * x1)))) ∂μ ∂μ ∂μ ∂μ :=
      p4Q2PZ37ABO2_integral_finFour _ (h2.mul (h3.mul (h0.mul (h1.mul hChar))))
    _ = n^4 * χ ((y 2)⁻¹ * (y 3)⁻¹ * y 0 * y 1) := by
      simp_rw [integral_const_mul]
      simp_rw [hOne1, p4Q2PZ37ABO2_integral_middle_constant,
        hOne0, p4Q2PZ37ABO2_integral_middle_constant,
        hOne3, p4Q2PZ37ABO2_integral_middle_constant, hOne2]
      ring
    _ = (p4Q2PZ37ABN_originalTemporalWilsonCharacterMoment b)^4 *
        χ (haarFinFourCyclicPlaquetteWord y) := by
      rw [p4Q2PZ37ABO2_word_eq]

/-- The genuine four-link temporal convolution of the original cyclic
plaquette character, divided by its actual positive product Haar mass. -/
noncomputable def p4Q2PZ37ABO2_originalFourLinkCharacterTransfer
    (b : ℝ) (y : X) : ℝ :=
  (∫ x : X, p4Q2PZ37ABO2_originalFourLinkWilsonKernel b x y *
    χ (haarFinFourCyclicPlaquetteWord x) ∂ν) /
      (p4Q2PZ37ABN_originalTemporalWilsonMass b)^4

/-- Exact original normalized four-link eigenlaw with the actual r_b^4.
It holds for every real b, and r_b's positive interval bounds are the
independently proved original-kernel results of ABN. -/
theorem p4Q2PZ37ABO2_originalFourLinkCharacterTransfer_eq_coefficient_pow_mul
    (b : ℝ) (y : X) :
    p4Q2PZ37ABO2_originalFourLinkCharacterTransfer b y =
      (p4Q2PZ37ABN_originalTemporalWilsonCoefficient b)^4 *
        χ (haarFinFourCyclicPlaquetteWord y) := by
  unfold p4Q2PZ37ABO2_originalFourLinkCharacterTransfer
  rw [p4Q2PZ37ABO2_originalFourLinkCharacter_convolution]
  unfold p4Q2PZ37ABN_originalTemporalWilsonCoefficient
  rw [div_pow]
  ring

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABO2_originalFourLinkWilsonKernel_mass
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABO2_originalFourLinkWilsonKernel_normalized_mass
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABO2_originalFourLinkCharacter_convolution
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABO2_originalFourLinkCharacterTransfer_eq_coefficient_pow_mul
