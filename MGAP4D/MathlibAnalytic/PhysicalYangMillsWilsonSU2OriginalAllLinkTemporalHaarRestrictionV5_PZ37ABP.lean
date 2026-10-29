import MGAP4D.MathlibAnalytic.FiniteProductWeightedEmbeddingIntegral
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPlaquetteTemporalHaarFloorV5_PZ37ABO3
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ABP — original all-link temporal Haar restriction

The left-hand side below is the ORIGINAL temporal-gauge crossing kernel
on the complete actual spatial-link carrier, not a newly substituted
four-link kernel. Split that finite carrier into the range of MY's
injective four-actual-edge embedding and its complement. Product Haar
transport and Fubini integrate every remote temporal factor to its true
one-link mass Z_b. After division by Z_b^(card Link), precisely ABO's
four factors remain, divided by Z_b^4.

The exact identity holds at every real coupling, every finite H, every
actual plaquette p (including H=0), and every real selected test in Lean's
total-integral convention. Continuous tests are genuinely integrable by
the separate theorem below. Character and centered-half-energy tests
therefore inherit ABO3's exact all-spatial-Haar moments and positive floor.

This closes the all-link TEMPORAL restriction input. It does not eliminate
the original spatial half-weights, identify Z_b^(card Link) with the true
physical transfer norm t, alter either interacting posterior, control
Perron factors or full-source cancellation, or prove a physical GI floor.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators Classical

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "μ" => normalizedCompactHaar G
local notation "ν" => Measure.pi (fun _ : Fin 4 => μ)
local notation "k" => specialUnitaryWilsonBoltzmannCentralFunction 2

local instance p4Q2PZ37ABP_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ABP_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ABP_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ABP_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ABP_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ABP_probability : IsProbabilityMeasure μ :=
  normalizedCompactHaar_isProbabilityMeasure G

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "haar" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "K" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel H 2
local instance p4Q2PZ37ABP_linkFintype : Fintype Link := Fintype.ofFinite _

private theorem p4Q2PZ37ABP_originalAllLinkKernel_eq_prod
    (b : ℝ) (A B : Cfg) :
    K b A B = ∏ e : Link, k b ((A e)⁻¹ * B e) := by
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
  have hnodup : (periodicHypercubicEvenSpatialSliceLinkList H).Nodup := by
    simp [periodicHypercubicEvenSpatialSliceLinkList]
  have hset : (periodicHypercubicEvenSpatialSliceLinkList H).toFinset =
      (Finset.univ : Finset Link) := by
    ext e
    simp
  calc
    _ = ∏ e ∈ (periodicHypercubicEvenSpatialSliceLinkList H).toFinset,
        specialUnitaryWilsonRelativeKernel 2 b (A e) (B e) :=
      (List.prod_toFinset
        (fun e : Link => specialUnitaryWilsonRelativeKernel 2 b (A e) (B e)) hnodup).symm
    _ = ∏ e : Link, k b ((A e)⁻¹ * B e) := by
      rw [hset]
      rfl

/-- The exact genuine Haar mass of the unchanged complete temporal
crossing kernel is Z_b raised to the number of ALL actual spatial links. -/
theorem p4Q2PZ37ABP_originalAllLinkWilsonKernel_mass
    (b : ℝ) (B : Cfg) :
    (∫ A : Cfg, K b A B ∂haar) =
      (p4Q2PZ37ABN_originalTemporalWilsonMass b)^(Fintype.card Link) := by
  simp_rw [p4Q2PZ37ABP_originalAllLinkKernel_eq_prod]
  change (∫ A : Link → G, ∏ e : Link, k b ((A e)⁻¹ * B e)
    ∂(Measure.pi fun _ : Link => μ)) = _
  simpa only [p4Q2PZ37ABO_originalOneLink_mass,
    Finset.prod_const, Finset.card_univ] using
    (integral_fintype_prod_eq_prod
      (ι := Link) (𝕜 := ℝ) (E := fun _ : Link => G)
      (μ := fun _ : Link => μ)
      (fun (e : Link) (x : G) => k b (x⁻¹ * B e)))

/-- Every remote coordinate is integrated with its original target link
and contributes exactly Z_b. The complementary set is the actual
complement of the four-edge embedding, not an assumed remote law. -/
theorem p4Q2PZ37ABP_originalRemoteTemporalWilson_mass
    (b : ℝ) (p : Plaq) (B : Cfg) :
    (∫ x : ({e : Link //
        e ∉ Set.range (p4Q2MY_originalPlaquetteFourEdgeEmbedding H p)} → G),
      ∏ e : {e : Link // e ∉ Set.range (p4Q2MY_originalPlaquetteFourEdgeEmbedding H p)},
        k b ((x e)⁻¹ * B e)
      ∂(Measure.pi fun _ : {e : Link //
        e ∉ Set.range (p4Q2MY_originalPlaquetteFourEdgeEmbedding H p)} => μ)) =
      (p4Q2PZ37ABN_originalTemporalWilsonMass b)^
        (Fintype.card {e : Link //
          e ∉ Set.range (p4Q2MY_originalPlaquetteFourEdgeEmbedding H p)}) := by
  let Remote : Type :=
    {e : Link // e ∉ Set.range (p4Q2MY_originalPlaquetteFourEdgeEmbedding H p)}
  simpa only [p4Q2PZ37ABO_originalOneLink_mass,
    Finset.prod_const, Finset.card_univ] using
    (integral_fintype_prod_eq_prod
      (ι := Remote) (𝕜 := ℝ) (E := fun _ : Remote => G)
      (μ := fun _ : Remote => μ)
      (fun (e : Remote) (x : G) => k b (x⁻¹ * B e.1)))

/-- Continuous tests of the four actual links are genuinely integrable
against the original complete temporal kernel and spatial Haar. -/
theorem p4Q2PZ37ABP_originalAllLinkWilson_test_integrable
    (b : ℝ) (p : Plaq) (B : Cfg) (f : (Fin 4 → G) → ℝ)
    (hf : Continuous f) :
    Integrable (fun A : Cfg => K b A B *
      f (fun i : Fin 4 => A (p4Q2MY_originalPlaquetteFourEdges H p i))) haar := by
  have hPair : Continuous (fun A : Cfg => (A, B)) :=
    (continuous_id : Continuous (fun A : Cfg => A)).prodMk
      (continuous_const : Continuous (fun _ : Cfg => B))
  have hJoint : Continuous (fun q : Cfg × Cfg => K b q.1 q.2) :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel_continuous H 2 b
  have hKernel : Continuous (fun A : Cfg => K b A B) :=
    hJoint.comp hPair
  have hCoordinates : Continuous
      (fun A : Cfg => fun i : Fin 4 => A (p4Q2MY_originalPlaquetteFourEdges H p i)) :=
    continuous_pi (fun i => continuous_apply (p4Q2MY_originalPlaquetteFourEdges H p i))
  exact (hKernel.mul (hf.comp hCoordinates)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Exact normalized all-link to actual-four-edge Haar restriction.
The full original kernel and its full normalization appear explicitly.
No posterior independence or four-link replacement is a premise. -/
theorem p4Q2PZ37ABP_originalAllLinkWilson_haar_restriction
    (b : ℝ) (p : Plaq) (B : Cfg) (f : (Fin 4 → G) → ℝ) :
    (∫ A : Cfg, K b A B *
      f (fun i : Fin 4 => A (p4Q2MY_originalPlaquetteFourEdges H p i)) ∂haar) /
        (p4Q2PZ37ABN_originalTemporalWilsonMass b)^(Fintype.card Link) =
    (∫ x : Fin 4 → G,
      p4Q2PZ37ABO2_originalFourLinkWilsonKernel b x
        (fun i : Fin 4 => B (p4Q2MY_originalPlaquetteFourEdges H p i)) * f x ∂ν) /
          (p4Q2PZ37ABN_originalTemporalWilsonMass b)^4 := by
  let z : ℝ := p4Q2PZ37ABN_originalTemporalWilsonMass b
  let w : Link → G → ℝ := fun e x => k b (x⁻¹ * B e) / z
  have hw (e : Link) : (∫ x : G, w e x ∂μ) = 1 := by
    dsimp [w]
    rw [integral_div, p4Q2PZ37ABO_originalOneLink_mass]
    exact div_self (p4Q2PZ37ABN_originalTemporalWilsonMass_pos b).ne'
  have hRestriction := integral_finiteProduct_mul_embedding_of_mass_one μ
    (p4Q2MY_originalPlaquetteFourEdgeEmbedding H p) w f hw
  have hAll (A : Cfg) : (∏ e : Link, w e (A e)) *
      f (fun i : Fin 4 => A (p4Q2MY_originalPlaquetteFourEdges H p i)) =
      (K b A B * f (fun i : Fin 4 => A (p4Q2MY_originalPlaquetteFourEdges H p i))) /
        z^(Fintype.card Link) := by
    rw [p4Q2PZ37ABP_originalAllLinkKernel_eq_prod]
    simp only [w, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ]
    ring
  have hFour (x : Fin 4 → G) :
      (∏ i : Fin 4, w (p4Q2MY_originalPlaquetteFourEdgeEmbedding H p i) (x i)) * f x =
      (p4Q2PZ37ABO2_originalFourLinkWilsonKernel b x
        (fun i : Fin 4 => B (p4Q2MY_originalPlaquetteFourEdges H p i)) * f x) / z^4 := by
    change (∏ i : Fin 4, k b ((x i)⁻¹ *
        B (p4Q2MY_originalPlaquetteFourEdges H p i)) / z) * f x =
      ((∏ i : Fin 4, k b ((x i)⁻¹ *
        B (p4Q2MY_originalPlaquetteFourEdges H p i))) * f x) / z^4
    simp only [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    ring
  change
    (∫ A : Cfg, (∏ e : Link, w e (A e)) *
      f (fun i : Fin 4 => A (p4Q2MY_originalPlaquetteFourEdges H p i)) ∂haar) =
    (∫ x : Fin 4 → G,
      (∏ i : Fin 4, w (p4Q2MY_originalPlaquetteFourEdgeEmbedding H p i) (x i)) * f x ∂ν)
      at hRestriction
  simp_rw [hAll, hFour] at hRestriction
  simpa only [integral_div, z] using hRestriction

/-- ABO3's character transmission is the normalized integral of the
ORIGINAL all-link temporal kernel, now proved rather than substituted. -/
theorem p4Q2PZ37ABP_originalAllLinkWilson_character_restriction
    (b : ℝ) (p : Plaq) (B : Cfg) :
    (∫ A : Cfg, K b A B *
      (1 - p4Q2LO_originalLocalPlaquetteContinuous H p A) ∂haar) /
        (p4Q2PZ37ABN_originalTemporalWilsonMass b)^(Fintype.card Link) =
      p4Q2PZ37ABO3_originalPlaquetteCharacterTransfer H b p B := by
  have h := p4Q2PZ37ABP_originalAllLinkWilson_haar_restriction H b p B
    (fun x => p4Q2PZ35C_originalOneLinkCharacter (haarFinFourCyclicPlaquetteWord x))
  simpa only [p4Q2PZ37ABO3_originalPlaquetteCharacterTransfer,
    p4Q2PZ37ABO2_originalFourLinkCharacterTransfer,
    p4Q2PZ35C_originalOneLinkCharacter,
    p4Q2MY_originalSpatialPlaquette_energy_eq_cyclic,
    p4Q2MY_originalPlaquetteCyclicHolonomy] using h

/-- The centered physical plaquette half-energy integrated against ALL
original temporal links, with the complete true temporal Haar mass. -/
noncomputable def p4Q2PZ37ABP_originalAllLinkCenteredTemporalTransfer
    (b : ℝ) (p : Plaq) (B : Cfg) : ℝ :=
  (∫ A : Cfg, K b A B *
    ((p4Q2LO_originalLocalPlaquetteContinuous H p A - 1) / 2) ∂haar) /
      (p4Q2PZ37ABN_originalTemporalWilsonMass b)^(Fintype.card Link)

/-- The exact original all-link integral equals ABO3's evaluated
four-link integral at every actual plaquette and every finite volume. -/
theorem p4Q2PZ37ABP_originalAllLinkCenteredTemporalTransfer_eq_fourLink
    (b : ℝ) (p : Plaq) (B : Cfg) :
    p4Q2PZ37ABP_originalAllLinkCenteredTemporalTransfer H b p B =
      p4Q2PZ37ABO3_originalPlaquetteCenteredTemporalTransfer H b p B := by
  have h := p4Q2PZ37ABP_originalAllLinkWilson_haar_restriction H b p B
    (fun x => (specialUnitaryWilsonPlaquetteEnergy 2
      (haarFinFourCyclicPlaquetteWord x) - 1) / 2)
  simpa only [p4Q2PZ37ABP_originalAllLinkCenteredTemporalTransfer,
    p4Q2PZ37ABO3_originalPlaquetteCenteredTemporalTransfer,
    p4Q2MY_originalSpatialPlaquette_energy_eq_cyclic,
    p4Q2MY_originalPlaquetteCyclicHolonomy] using h

/-- The original all-link temporal centered half-energy has the exact
coefficient r_b^4. This concerns temporal reference-Haar convolution. -/
theorem p4Q2PZ37ABP_originalAllLinkCenteredTemporalTransfer_eq_coefficient_pow_mul
    (b : ℝ) (p : Plaq) (B : Cfg) :
    p4Q2PZ37ABP_originalAllLinkCenteredTemporalTransfer H b p B =
      (p4Q2PZ37ABN_originalTemporalWilsonCoefficient b)^4 *
        ((p4Q2LO_originalLocalPlaquetteContinuous H p B - 1) / 2) := by
  rw [p4Q2PZ37ABP_originalAllLinkCenteredTemporalTransfer_eq_fourLink,
    p4Q2PZ37ABO3_originalPlaquetteCenteredTemporalTransfer_eq_coefficient_pow_mul]

/-- Exact all-spatial-Haar second moment for the unchanged all-link
temporal transfer: r_b^8/16, independently of finite H and actual p. -/
theorem p4Q2PZ37ABP_originalAllLinkCenteredTemporalTransfer_haar_secondMoment
    (b : ℝ) (p : Plaq) :
    (∫ B : Cfg, (p4Q2PZ37ABP_originalAllLinkCenteredTemporalTransfer H b p B)^2 ∂haar) =
      (p4Q2PZ37ABN_originalTemporalWilsonCoefficient b)^8 / 16 := by
  simp_rw [p4Q2PZ37ABP_originalAllLinkCenteredTemporalTransfer_eq_fourLink]
  exact p4Q2PZ37ABO3_originalPlaquetteCenteredTemporalTransfer_haar_secondMoment H b p

/-- ABO3's common positive reference-Haar floor now applies to the
original ALL-LINK temporal convolution. Interacting GI floors remain open. -/
theorem p4Q2PZ37ABP_originalAllLinkCenteredTemporalTransfer_positive_interval
    (b0 B b : ℝ) (hb0 : 0 < b0) (hLower : b0 ≤ b) (hUpper : b ≤ B)
    (p : Plaq) :
    0 < (b0 * Real.exp (-2 * B) / 4)^8 / 16 ∧
      (b0 * Real.exp (-2 * B) / 4)^8 / 16 ≤
        ∫ A : Cfg, (p4Q2PZ37ABP_originalAllLinkCenteredTemporalTransfer H b p A)^2 ∂haar := by
  simp_rw [p4Q2PZ37ABP_originalAllLinkCenteredTemporalTransfer_eq_fourLink]
  exact p4Q2PZ37ABO3_originalPlaquetteCenteredTemporalTransfer_positive_interval
    H b0 B b hb0 hLower hUpper p

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABP_originalAllLinkWilsonKernel_mass
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABP_originalRemoteTemporalWilson_mass
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABP_originalAllLinkWilson_test_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABP_originalAllLinkWilson_haar_restriction
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABP_originalAllLinkWilson_character_restriction
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABP_originalAllLinkCenteredTemporalTransfer_eq_fourLink
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABP_originalAllLinkCenteredTemporalTransfer_eq_coefficient_pow_mul
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABP_originalAllLinkCenteredTemporalTransfer_haar_secondMoment
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABP_originalAllLinkCenteredTemporalTransfer_positive_interval
