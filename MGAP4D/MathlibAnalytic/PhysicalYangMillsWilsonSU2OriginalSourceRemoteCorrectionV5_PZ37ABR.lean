import MGAP4D.MathlibAnalytic.FiniteProductEmbeddingKernelIntegral
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalRemotePerronMarginalV5_PZ37ABQ2
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ABR — exact original-source remote correction

ABQ2 integrates Omega(A)*K(A,B). An original source inserted against
K(A,B) must not silently acquire this extra source-side Perron factor.
Define the actual remote integral S with the original spatial half-weight
but WITHOUT Omega(A), separately from ABQ2's R. The exact positive
correction V=S/R restores the original source.

The normalized four-edge density is the true Perron marginal. Its mass
is normalized using ABQ2's actual mass, so hW(B)*mass=t*Omega(B).
Neither the temporal mass Z^4 nor Z^|Link| is substituted for t.

This is an original-kernel source representation and a signed decomposition.
It does not identify a source with Omega times that source, replace either
interacting GI posterior, prove a signed GI lower bound, control the full
negative tail, or close any continuum mass-gap obligation.
-/

namespace MGAP4D.MathlibAnalytic
open MeasureTheory
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 1000000

local instance p4Q2PZ37ABR_finTwoFintype : Fintype (Fin 2) := Fin.fintype 2
local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "X" => Fin 4 → G
local notation "μ" => normalizedCompactHaar G
local instance p4Q2PZ37ABR_group : IsTopologicalGroup G := specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ABR_compact : CompactSpace G := specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ABR_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ABR_measurable : MeasurableSpace G :=
  oneSlabHaarL2SpecialUnitaryMeasurableSpace 2
local instance p4Q2PZ37ABR_borel : BorelSpace G := specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ABR_probability : IsProbabilityMeasure μ :=
  normalizedCompactHaar_isProbabilityMeasure G

namespace GroundStatePosteriorJoint
variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local instance p4Q2PZ37ABR_linkDecEq : DecidableEq Link :=
  fun a b => Classical.propDecidable (a = b)
local instance p4Q2PZ37ABR_links : Fintype Link := Fintype.ofFinite _
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "hW" => periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight H 2
local notation "K" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2
local notation "Ω" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
  H 2 (by norm_num)
local notation "W" => p4Q2PZ37ABQ_originalSpatialPerronWeight H

private theorem p4Q2PZ37ABR_crossing_eq_prod (b : ℝ) (A B : Cfg) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel H 2 b A B =
      ∏ e : Link, specialUnitaryWilsonRelativeKernel 2 b (A e) (B e) := by
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
  have hn : (periodicHypercubicEvenSpatialSliceLinkList H).Nodup := by
    unfold periodicHypercubicEvenSpatialSliceLinkList
    exact Finset.nodup_toList _
  have hs : (periodicHypercubicEvenSpatialSliceLinkList H).toFinset =
      (Finset.univ : Finset Link) := by ext e; simp
  rw [← List.prod_toFinset
    (fun e : Link => specialUnitaryWilsonRelativeKernel 2 b (A e) (B e)) hn, hs]

variable (p : PeriodicHypercubicEvenSpatialSlicePlaquette H)
include p
local notation "emb" => p4Q2MY_originalPlaquetteFourEdgeEmbedding H p
local notation "Remote" => {e : Link // e ∉ Set.range emb}
local notation "ρ" => Measure.pi (fun _ : Remote => μ)
local notation "ν" => Measure.pi (fun _ : Fin 4 => μ)
local notation "assemble" => finiteProductEmbeddingAssemble emb
local notation "R" => p4Q2PZ37ABQ2_originalRemotePerronWeight H p
local notation "Kr" => p4Q2PZ37ABQ2_originalRemoteTemporalKernel H p
local notation "K4" => p4Q2PZ37ABO2_originalFourLinkWilsonKernel

private theorem p4Q2PZ37ABR_remote_continuous (b : ℝ) (B : Cfg) :
    Continuous (Kr b B) := by
  unfold p4Q2PZ37ABQ2_originalRemoteTemporalKernel
  exact continuous_finset_prod _ (fun e _ =>
    (continuous_specialUnitaryWilsonRelativeKernel 2 b).comp₂
      (continuous_apply e) continuous_const)

private theorem p4Q2PZ37ABR_remote_pos (b : ℝ) (B : Cfg) (r : Remote → G) :
    0 < Kr b B r := by
  unfold p4Q2PZ37ABQ2_originalRemoteTemporalKernel
  apply Finset.prod_pos
  intro e _
  change 0 < Real.exp _
  exact Real.exp_pos _

private theorem p4Q2PZ37ABR_four_continuous (b : ℝ) (B : Cfg) :
    Continuous (fun x : X => K4 b x (fun i => B (emb i))) := by
  change Continuous (fun x : X =>
    ∏ i : Fin 4, specialUnitaryWilsonRelativeKernel 2 b (x i) (B (emb i)))
  exact continuous_finset_prod _ (fun i _ =>
    (continuous_specialUnitaryWilsonRelativeKernel 2 b).comp₂
      (continuous_apply i) continuous_const)

private theorem p4Q2PZ37ABR_four_pos (b : ℝ) (B : Cfg) (x : X) :
    0 < K4 b x (fun i => B (emb i)) := by
  unfold p4Q2PZ37ABO2_originalFourLinkWilsonKernel
  apply Finset.prod_pos
  intro i _
  change 0 < Real.exp _
  exact Real.exp_pos _

/-- Actual remote weight for an original kernel source, without inserting
Omega(A). Every original remote temporal factor is retained. -/
noncomputable def p4Q2PZ37ABR_originalRemoteSourceWeight
    (b : ℝ) (B : Cfg) (x : X) : ℝ :=
  ∫ r : Remote → G, hW b (assemble x r) * Kr b B r ∂ρ

local notation "S" => p4Q2PZ37ABR_originalRemoteSourceWeight H p

/-- Genuine integrability of the source-side remote integrand. -/
theorem p4Q2PZ37ABR_originalRemoteSourceWeight_integrable
    (b : ℝ) (B : Cfg) (x : X) :
    Integrable (fun r : Remote → G => hW b (assemble x r) * Kr b B r) ρ := by
  have ha : Continuous (fun r : Remote → G => assemble x r) :=
    (finiteProductEmbeddingAssemble_continuous emb).comp
      ((continuous_const : Continuous (fun _ : Remote → G => x)).prodMk continuous_id)
  have hc := ((periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight_continuous H 2 b).comp ha).mul
    (p4Q2PZ37ABR_remote_continuous H p b B)
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Strict positivity is proved using integrability, not the total-integral convention. -/
theorem p4Q2PZ37ABR_originalRemoteSourceWeight_pos
    (b : ℝ) (B : Cfg) (x : X) : 0 < S b B x := by
  apply integral_pos_of_forall_pos_probability ρ _
    (p4Q2PZ37ABR_originalRemoteSourceWeight_integrable H p b B x)
  intro r
  apply mul_pos _ (p4Q2PZ37ABR_remote_pos H p b B r)
  change 0 < Real.exp _
  exact Real.exp_pos _

/-- Continuity of the actual source-side remote integral. -/
theorem p4Q2PZ37ABR_originalRemoteSourceWeight_continuous
    (b : ℝ) (B : Cfg) : Continuous (S b B) := by
  have hc : Continuous (fun z : X × (Remote → G) =>
      hW b (assemble z.1 z.2) * Kr b B z.2) :=
    ((periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight_continuous H 2 b).comp
      (finiteProductEmbeddingAssemble_continuous emb)).mul
        ((p4Q2PZ37ABR_remote_continuous H p b B).comp continuous_snd)
  exact continuous_compactParameter_integral ρ _ hc

/-- ABQ2's actual Perron remote integral is continuous as a four-edge function. -/
theorem p4Q2PZ37ABR_originalRemotePerronWeight_continuous
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) : Continuous (R b hb B) := by
  have hc : Continuous (fun z : X × (Remote → G) =>
      W b hb (assemble z.1 z.2) * Kr b B z.2) :=
    ((p4Q2PZ37ABQ2_originalWeight_continuous H b hb).comp
      (finiteProductEmbeddingAssemble_continuous emb)).mul
        ((p4Q2PZ37ABR_remote_continuous H p b B).comp continuous_snd)
  exact continuous_compactParameter_integral ρ _ hc

attribute [local irreducible]
  p4Q2MY_originalPlaquetteFourEdgeEmbedding
  finiteProductEmbeddingAssemble

/-- Exact original kernel section, without a source-side vacuum insertion. -/
theorem p4Q2PZ37ABR_originalKernelSection_withoutVacuum
    (b : ℝ) (B : Cfg) (f : X → ℝ) (hf : Continuous f) :
    (∫ A : Cfg, K b A B * f (fun i => A (emb i)) ∂haar) =
      hW b B * ∫ x : X, K4 b x (fun i => B (emb i)) * S b B x * f x ∂ν := by
  let q : Link → G → ℝ := fun e a => specialUnitaryWilsonRelativeKernel 2 b a (B e)
  have hq (e : Link) : Continuous (q e) :=
    (continuous_specialUnitaryWilsonRelativeKernel 2 b).comp₂ continuous_id continuous_const
  have hraw := integral_finiteProductEmbedding_weightedKernel μ emb q hq (hW b)
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight_continuous H 2 b) f hf
  have hhaar : haar = (Measure.pi fun _ : Link => μ) := rfl
  rw [← hhaar] at hraw
  have hfour (x : X) : (∏ i : Fin 4, q (emb i) (x i)) =
      K4 b x (fun i => B (emb i)) := by
    unfold p4Q2PZ37ABO2_originalFourLinkWilsonKernel
    rfl
  have hremote (x : X) :
      (∫ r : Remote → G, hW b (assemble x r) *
        (∏ e : Remote, q e.1 (r e)) ∂ρ) = S b B x := rfl
  calc
    _ = hW b B * ∫ A : Cfg,
        hW b A * (∏ e : Link, q e (A e)) * f (fun i => A (emb i)) ∂haar := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with A
      unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
      rw [p4Q2PZ37ABR_crossing_eq_prod H b A B]
      dsimp only [q]
      ring
    _ = _ := by
      rw [hraw]
      congr 1

/-- Exact correction for the original source, not a replacement physical source. -/
noncomputable def p4Q2PZ37ABR_originalSourceCorrection
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (x : X) : ℝ := S b B x / R b hb B x
local notation "V" => p4Q2PZ37ABR_originalSourceCorrection H p

/-- Both actual remote weights are strictly positive. -/
theorem p4Q2PZ37ABR_originalSourceCorrection_pos
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (x : X) : 0 < V b hb B x :=
  div_pos (p4Q2PZ37ABR_originalRemoteSourceWeight_pos H p b B x)
    (p4Q2PZ37ABQ2_originalRemotePerronWeight_pos H p b hb B x)

/-- The exact correction is continuous. -/
theorem p4Q2PZ37ABR_originalSourceCorrection_continuous
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) : Continuous (V b hb B) :=
  (p4Q2PZ37ABR_originalRemoteSourceWeight_continuous H p b B).div
    (p4Q2PZ37ABR_originalRemotePerronWeight_continuous H p b hb B)
    (fun x => (p4Q2PZ37ABQ2_originalRemotePerronWeight_pos H p b hb B x).ne')

/-- Multiplying by the correction recovers S exactly, not approximately. -/
theorem p4Q2PZ37ABR_perronWeight_mul_sourceCorrection
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (x : X) : R b hb B x * V b hb B x = S b B x := by
  change R b hb B x * (S b B x / R b hb B x) = S b B x
  rw [mul_comm]
  exact div_mul_cancel₀ _ (p4Q2PZ37ABQ2_originalRemotePerronWeight_pos H p b hb B x).ne'

/-- The actual four-edge Perron mass before the target half-weight. -/
noncomputable def p4Q2PZ37ABR_originalFourEdgePerronMass
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) : ℝ :=
  ∫ x : X, K4 b x (fun i => B (emb i)) * R b hb B x ∂ν
local notation "M" => p4Q2PZ37ABR_originalFourEdgePerronMass H p

/-- Actual integrability and strict positivity of the four-edge Perron mass. -/
theorem p4Q2PZ37ABR_originalFourEdgePerronMass_pos
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) : 0 < M b hb B := by
  have hc := (p4Q2PZ37ABR_four_continuous H p b B).mul
    (p4Q2PZ37ABR_originalRemotePerronWeight_continuous H p b hb B)
  apply integral_pos_of_forall_pos_probability ν _
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  intro x
  exact mul_pos (p4Q2PZ37ABR_four_pos H p b B x)
    (p4Q2PZ37ABQ2_originalRemotePerronWeight_pos H p b hb B x)

/-- ABQ2's original physical normalization is retained exactly. -/
theorem p4Q2PZ37ABR_originalFourEdgePerronMass_trueNormalization
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) :
    hW b B * M b hb B =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) b hb‖ * Ω b hb B :=
  p4Q2PZ37ABQ2_originalKernelSection_fourEdge_mass H p b hb B

/-- Density of the genuine Perron four-edge marginal relative to four-fold Haar. -/
noncomputable def p4Q2PZ37ABR_originalPerronFourEdgeDensity
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (x : X) : ℝ :=
  (K4 b x (fun i => B (emb i)) * R b hb B x) / M b hb B
local notation "D" => p4Q2PZ37ABR_originalPerronFourEdgeDensity H p

/-- Pointwise strict positivity of the normalized actual marginal. -/
theorem p4Q2PZ37ABR_originalPerronFourEdgeDensity_pos
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (x : X) : 0 < D b hb B x :=
  div_pos (mul_pos (p4Q2PZ37ABR_four_pos H p b B x)
    (p4Q2PZ37ABQ2_originalRemotePerronWeight_pos H p b hb B x))
    (p4Q2PZ37ABR_originalFourEdgePerronMass_pos H p b hb B)

/-- Continuity of the actual normalized density. -/
theorem p4Q2PZ37ABR_originalPerronFourEdgeDensity_continuous
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) : Continuous (D b hb B) :=
  ((p4Q2PZ37ABR_four_continuous H p b B).mul
    (p4Q2PZ37ABR_originalRemotePerronWeight_continuous H p b hb B)).div_const _

/-- Mass one with the genuine marginal mass, not the temporal product mass. -/
theorem p4Q2PZ37ABR_originalPerronFourEdgeDensity_mass_one
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) : (∫ x : X, D b hb B x ∂ν) = 1 := by
  unfold p4Q2PZ37ABR_originalPerronFourEdgeDensity
  rw [integral_div]
  exact div_self (p4Q2PZ37ABR_originalFourEdgePerronMass_pos H p b hb B).ne'

/-- The original source integral is represented by the true Perron marginal
ONLY with its actual V=S/R correction. The physical factor is t*Omega(B). -/
theorem p4Q2PZ37ABR_originalKernelSection_correctedPerronDensity
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (f : X → ℝ) (hf : Continuous f) :
    (∫ A : Cfg, K b A B * f (fun i => A (emb i)) ∂haar) =
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) b hb‖ * Ω b hb B) *
          ∫ x : X, D b hb B x * V b hb B x * f x ∂ν := by
  have hm : M b hb B ≠ 0 :=
    (p4Q2PZ37ABR_originalFourEdgePerronMass_pos H p b hb B).ne'
  have hd (x : X) : M b hb B * D b hb B x =
      K4 b x (fun i => B (emb i)) * R b hb B x := by
    unfold p4Q2PZ37ABR_originalPerronFourEdgeDensity
    rw [mul_comm]
    exact div_mul_cancel₀ _ hm
  have hi : (∫ x : X, K4 b x (fun i => B (emb i)) * S b B x * f x ∂ν) =
      M b hb B * ∫ x : X, D b hb B x * V b hb B x * f x ∂ν := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    calc
      _ = K4 b x (fun i => B (emb i)) * (R b hb B x * V b hb B x) * f x := by
        rw [p4Q2PZ37ABR_perronWeight_mul_sourceCorrection]
      _ = (M b hb B * D b hb B x) * V b hb B x * f x := by rw [hd]; ring
      _ = _ := by ring
  rw [p4Q2PZ37ABR_originalKernelSection_withoutVacuum H p b B f hf, hi,
    ← mul_assoc, p4Q2PZ37ABR_originalFourEdgePerronMass_trueNormalization]

/-- Exact positive-minus-negative decomposition of the corrected signed
source integral. Neither part may be omitted in a lower-bound argument. -/
theorem p4Q2PZ37ABR_correctedSignedIntegral_parts
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (f : X → ℝ) (hf : Continuous f) :
    (∫ x : X, D b hb B x * V b hb B x * f x ∂ν) =
      (∫ x : X, D b hb B x * V b hb B x * max (f x) 0 ∂ν) -
        (∫ x : X, D b hb B x * V b hb B x * max (-(f x)) 0 ∂ν) := by
  have hw := (p4Q2PZ37ABR_originalPerronFourEdgeDensity_continuous H p b hb B).mul
    (p4Q2PZ37ABR_originalSourceCorrection_continuous H p b hb B)
  have hp : Integrable (fun x : X =>
      D b hb B x * V b hb B x * max (f x) 0) ν :=
    (hw.mul (hf.max continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hn : Integrable (fun x : X =>
      D b hb B x * V b hb B x * max (-(f x)) 0) ν :=
    (hw.mul (hf.neg.max continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [← integral_sub hp hn]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : 0 ≤ f x
  · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]
    ring
  · have hx' : f x ≤ 0 := le_of_lt (lt_of_not_ge hx)
    rw [max_eq_right hx', max_eq_left (neg_nonneg.mpr hx')]
    ring

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABR_originalRemoteSourceWeight_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABR_originalRemoteSourceWeight_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABR_originalRemoteSourceWeight_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABR_originalRemotePerronWeight_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABR_originalKernelSection_withoutVacuum
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABR_originalSourceCorrection_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABR_originalSourceCorrection_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABR_perronWeight_mul_sourceCorrection
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABR_originalFourEdgePerronMass_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABR_originalFourEdgePerronMass_trueNormalization
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABR_originalPerronFourEdgeDensity_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABR_originalPerronFourEdgeDensity_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABR_originalPerronFourEdgeDensity_mass_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABR_originalKernelSection_correctedPerronDensity
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABR_correctedSignedIntegral_parts
