import MGAP4D.MathlibAnalytic.FiniteProductEmbeddingAssemblyIntegral
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFourEdgeSpatialPerronHarnackV5_PZ37ABQ
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ABQ2 — actual remote-integrated spatial/Perron weight

Reassemble the actual four plaquette edges with the full actual complement.
Integrate the unchanged remote temporal Wilson factors against the original
spatial half-weight and the positive continuous Perron representative.
This gives a genuinely positive, integrable remote weight, with ABQ's
volume-independent exp(56*b) relative comparison after integration.

Product-Haar Fubini connects this weight to the ORIGINAL full one-slab
kernel section. Both spatial half-weights and the original Perron vacuum
remain present. Its mass is the TRUE transfer norm t times Omega(B), not
a power of the one-link temporal Haar mass. No signed GI response floor,
posterior independence, cancellation estimate, or continuum claim follows.
-/

namespace MGAP4D.MathlibAnalytic
open MeasureTheory
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 1000000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "μ" => normalizedCompactHaar G
local instance p4Q2PZ37ABQ2_group : IsTopologicalGroup G := specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ABQ2_compact : CompactSpace G := specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ABQ2_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ABQ2_measurable : MeasurableSpace G := specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ABQ2_borel : BorelSpace G := specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ABQ2_probability : IsProbabilityMeasure μ :=
  normalizedCompactHaar_isProbabilityMeasure G

namespace GroundStatePosteriorJoint
variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "haar" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "W" => p4Q2PZ37ABQ_originalSpatialPerronWeight H
local notation "Ω" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
  H 2 (by norm_num)
local notation "hW" => periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight H 2
local notation "K" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2
local instance p4Q2PZ37ABQ2_links : Fintype Link := Fintype.ofFinite _

/-- ABQ's boundary factor is the ORIGINAL spatial half-weight times Perron. -/
theorem p4Q2PZ37ABQ2_originalWeight_eq_halfWeight_mul_vacuum
    (b : ℝ) (hb : 0 ≤ b) (A : Cfg) :
    W b hb A = hW b A * Ω b hb A := by
  simp only [p4Q2PZ37ABQ_originalSpatialPerronWeight,
    periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight, neg_mul]

/-- The original spatial/Perron boundary factor is continuous. -/
theorem p4Q2PZ37ABQ2_originalWeight_continuous (b : ℝ) (hb : 0 ≤ b) :
    Continuous (W b hb) := by
  have h := (periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight_continuous H 2 b).mul
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_continuous
      H 2 (by norm_num) b hb)
  have hEq : W b hb = (fun A : Cfg => hW b A * Ω b hb A) := by
    funext A
    exact p4Q2PZ37ABQ2_originalWeight_eq_halfWeight_mul_vacuum H b hb A
  rw [hEq]
  simpa only [Pi.mul_apply] using h

variable (p : Plaq)
/-!
Lean 4 chooses section theorem parameters from theorem headers, not theorem
proofs. Since p occurs through local notation (emb/Remote/ρ/assemble), explicitly
include p so that generated declarations retain the actual plaquette index.
Without this the header elaborates as a free metavar and every subsequent
reference to p or a remote type may become an unknown free variable.
-/
include p
local notation "emb" => p4Q2MY_originalPlaquetteFourEdgeEmbedding H p
local notation "Remote" => {e : Link // e ∉ Set.range emb}
local notation "ρ" => Measure.pi (fun _ : Remote => μ)
local notation "ν" => Measure.pi (fun _ : Fin 4 => μ)
local notation "assemble" => finiteProductEmbeddingAssemble emb

/-- Every original remote temporal factor, with the original target B_e. -/
noncomputable def p4Q2PZ37ABQ2_originalRemoteTemporalKernel
    (b : ℝ) (B : Cfg) (r : Remote → G) : ℝ :=
  ∏ e : Remote, specialUnitaryWilsonRelativeKernel 2 b (r e) (B e.1)

private theorem p4Q2PZ37ABQ2_remoteKernel_continuous (b : ℝ) (B : Cfg) :
    Continuous (p4Q2PZ37ABQ2_originalRemoteTemporalKernel H p b B) := by
  unfold p4Q2PZ37ABQ2_originalRemoteTemporalKernel
  exact continuous_finset_prod _ (fun e _ =>
    (continuous_specialUnitaryWilsonRelativeKernel 2 b).comp₂
      (continuous_apply e) continuous_const)

private theorem p4Q2PZ37ABQ2_remoteKernel_pos (b : ℝ) (B : Cfg) (r : Remote → G) :
    0 < p4Q2PZ37ABQ2_originalRemoteTemporalKernel H p b B r := by
  unfold p4Q2PZ37ABQ2_originalRemoteTemporalKernel
  apply Finset.prod_pos
  intro e _
  change 0 < Real.exp _
  exact Real.exp_pos _

/-- This is the actual remote integral, including the interacting spatial
Wilson half-weight and the original Perron representative. -/
noncomputable def p4Q2PZ37ABQ2_originalRemotePerronWeight
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (x : Fin 4 → G) : ℝ :=
  ∫ r : Remote → G, W b hb (assemble x r) *
    p4Q2PZ37ABQ2_originalRemoteTemporalKernel H p b B r ∂ρ

/-- The remote integrand is genuinely integrable; the total-integral zero
convention is not being used to infer positivity or monotonicity. -/
theorem p4Q2PZ37ABQ2_originalRemotePerronWeight_integrable
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (x : Fin 4 → G) :
    Integrable (fun r : Remote → G => W b hb (assemble x r) *
      p4Q2PZ37ABQ2_originalRemoteTemporalKernel H p b B r) ρ := by
  have hAssemble : Continuous (fun r : Remote → G => assemble x r) :=
    (finiteProductEmbeddingAssemble_continuous emb).comp
      ((continuous_const : Continuous (fun _ : Remote → G => x)).prodMk continuous_id)
  have hcont := ((p4Q2PZ37ABQ2_originalWeight_continuous H b hb).comp hAssemble).mul
    (p4Q2PZ37ABQ2_remoteKernel_continuous H p b B)
  exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Every actual remote integral is strictly positive, including H=0. -/
theorem p4Q2PZ37ABQ2_originalRemotePerronWeight_pos
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (x : Fin 4 → G) :
    0 < p4Q2PZ37ABQ2_originalRemotePerronWeight H p b hb B x := by
  let F : (Remote → G) → ℝ := fun r => W b hb (assemble x r) *
    p4Q2PZ37ABQ2_originalRemoteTemporalKernel H p b B r
  have hpos (r : Remote → G) : 0 < F r :=
    mul_pos (p4Q2PZ37ABQ_originalSpatialPerronWeight_pos H b hb (assemble x r))
      (p4Q2PZ37ABQ2_remoteKernel_pos H p b B r)
  have hInt : Integrable F ρ :=
    p4Q2PZ37ABQ2_originalRemotePerronWeight_integrable H p b hb B x
  have hsupport : Function.support F = Set.univ := by
    ext r
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (hpos r).ne'
  change 0 < ∫ r, F r ∂ρ
  apply (integral_pos_iff_support_of_nonneg (fun r => (hpos r).le) hInt).mpr
  rw [hsupport, measure_univ]
  exact zero_lt_one

/-- The same remote temporal factors are used on both sides; integrating
ABQ's pointwise comparison retains exactly exp(56*b), uniformly in H. -/
theorem p4Q2PZ37ABQ2_originalRemotePerronWeight_le_exp
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (x y : Fin 4 → G) :
    p4Q2PZ37ABQ2_originalRemotePerronWeight H p b hb B x ≤
      Real.exp (56 * b) * p4Q2PZ37ABQ2_originalRemotePerronWeight H p b hb B y := by
  have hcompare (r : Remote → G) :
      W b hb (assemble x r) ≤ Real.exp (56 * b) * W b hb (assemble y r) := by
    apply p4Q2PZ37ABQ_originalSpatialPerronWeight_fourEdge_le H b hb p
    intro e he
    have hx := finiteProductEmbeddingAssemble_remote emb x r ⟨e, he⟩
    have hy := finiteProductEmbeddingAssemble_remote emb y r ⟨e, he⟩
    exact hx.trans hy.symm
  have hIntX := p4Q2PZ37ABQ2_originalRemotePerronWeight_integrable H p b hb B x
  have hIntY := p4Q2PZ37ABQ2_originalRemotePerronWeight_integrable H p b hb B y
  change (∫ r, W b hb (assemble x r) *
    p4Q2PZ37ABQ2_originalRemoteTemporalKernel H p b B r ∂ρ) ≤ _
  calc
    _ ≤ ∫ r, Real.exp (56 * b) * (W b hb (assemble y r) *
        p4Q2PZ37ABQ2_originalRemoteTemporalKernel H p b B r) ∂ρ := by
      apply integral_mono hIntX (hIntY.const_mul _)
      intro r
      have h := mul_le_mul_of_nonneg_right (hcompare r)
        (p4Q2PZ37ABQ2_remoteKernel_pos H p b B r).le
      simpa only [mul_assoc] using h
    _ = _ := integral_const_mul _ _

/-- Two-sided, volume-uniform relative comparison for the ACTUAL remote
integral. This is not an absolute lower bound on its total mass. -/
theorem p4Q2PZ37ABQ2_originalRemotePerronWeight_twoSided
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (x y : Fin 4 → G) :
    Real.exp (-(56 * b)) * p4Q2PZ37ABQ2_originalRemotePerronWeight H p b hb B y ≤
        p4Q2PZ37ABQ2_originalRemotePerronWeight H p b hb B x ∧
      p4Q2PZ37ABQ2_originalRemotePerronWeight H p b hb B x ≤
        Real.exp (56 * b) * p4Q2PZ37ABQ2_originalRemotePerronWeight H p b hb B y := by
  constructor
  · have h := mul_le_mul_of_nonneg_left
      (p4Q2PZ37ABQ2_originalRemotePerronWeight_le_exp H p b hb B y x)
      (Real.exp_nonneg (-(56 * b)))
    have hc : Real.exp (-(56 * b)) * Real.exp (56 * b) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    simpa only [← mul_assoc, hc, one_mul] using h
  · exact p4Q2PZ37ABQ2_originalRemotePerronWeight_le_exp H p b hb B x y

private theorem p4Q2PZ37ABQ2_crossing_eq_prod (b : ℝ) (A B : Cfg) :
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

private theorem p4Q2PZ37ABQ2_crossing_assemble
    (b : ℝ) (B : Cfg) (x : Fin 4 → G) (r : Remote → G) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel H 2 b (assemble x r) B =
      p4Q2PZ37ABO2_originalFourLinkWilsonKernel b x (fun i => B (emb i)) *
        p4Q2PZ37ABQ2_originalRemoteTemporalKernel H p b B r := by
  rw [p4Q2PZ37ABQ2_crossing_eq_prod]
  exact finiteProductEmbeddingAssemble_prod emb
    (fun e a => specialUnitaryWilsonRelativeKernel 2 b a (B e)) x r

private theorem p4Q2PZ37ABQ2_fullKernel_assemble
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (x : Fin 4 → G) (r : Remote → G) :
    Ω b hb (assemble x r) * K b (assemble x r) B =
      hW b B * (p4Q2PZ37ABO2_originalFourLinkWilsonKernel b x (fun i => B (emb i)) *
        (W b hb (assemble x r) * p4Q2PZ37ABQ2_originalRemoteTemporalKernel H p b B r)) := by
  rw [p4Q2PZ37ABQ2_originalWeight_eq_halfWeight_mul_vacuum]
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
  rw [p4Q2PZ37ABQ2_crossing_assemble H p b B x r]
  ring

/-- Exact four-edge formula for the ORIGINAL full one-slab Perron kernel
section. The remote spatial interactions and Perron weight are integrated,
not removed or replaced. The right spatial half-weight is retained. -/
theorem p4Q2PZ37ABQ2_originalKernelSection_fourEdge_integral
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (f : (Fin 4 → G) → ℝ) (hf : Continuous f) :
    (∫ A : Cfg, Ω b hb A * K b A B * f (fun i => A (emb i)) ∂haar) =
      hW b B * ∫ x : Fin 4 → G,
        p4Q2PZ37ABO2_originalFourLinkWilsonKernel b x (fun i => B (emb i)) *
          p4Q2PZ37ABQ2_originalRemotePerronWeight H p b hb B x * f x ∂ν := by
  let F : Cfg → ℝ := fun A => Ω b hb A * K b A B * f (fun i => A (emb i))
  have hPair : Continuous (fun A : Cfg => (A, B)) := continuous_id.prodMk continuous_const
  have hKernel := Continuous.comp'
    (f := fun A : Cfg => (A, B)) (g := fun z : Cfg × Cfg => K b z.1 z.2)
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous H 2 b) hPair
  change Continuous (fun A : Cfg => K b A B) at hKernel
  have hCoordinates : Continuous (fun A : Cfg => fun i : Fin 4 => A (emb i)) :=
    continuous_pi (fun i => continuous_apply (emb i))
  have hF : Continuous F :=
    ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_continuous
      H 2 (by norm_num) b hb).mul hKernel).mul (hf.comp hCoordinates)
  have hpoint (x : Fin 4 → G) (r : Remote → G) : F (assemble x r) =
      (hW b B * p4Q2PZ37ABO2_originalFourLinkWilsonKernel b x (fun i => B (emb i)) * f x) *
        (W b hb (assemble x r) * p4Q2PZ37ABQ2_originalRemoteTemporalKernel H p b B r) := by
    have hcoords : (fun i : Fin 4 => assemble x r (emb i)) = x := by
      funext i
      exact finiteProductEmbeddingAssemble_selected emb x r i
    dsimp only [F]
    rw [hcoords, p4Q2PZ37ABQ2_fullKernel_assemble H p b hb B x r]
    ring
  calc
    _ = ∫ x : Fin 4 → G, ∫ r : Remote → G, F (assemble x r) ∂ρ ∂ν :=
      integral_finiteProductEmbeddingAssemble μ emb F hF
    _ = ∫ x : Fin 4 → G,
        (hW b B * p4Q2PZ37ABO2_originalFourLinkWilsonKernel b x (fun i => B (emb i)) * f x) *
          p4Q2PZ37ABQ2_originalRemotePerronWeight H p b hb B x ∂ν := by
      apply integral_congr_ae
      filter_upwards with x
      simp_rw [hpoint]
      exact integral_const_mul _ _
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      ring

/-- The four-edge integral has the genuine physical normalization t*Omega(B).
The temporal product mass Z_b^|Link| is not substituted for t. -/
theorem p4Q2PZ37ABQ2_originalKernelSection_fourEdge_mass
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) :
    hW b B * (∫ x : Fin 4 → G,
      p4Q2PZ37ABO2_originalFourLinkWilsonKernel b x (fun i => B (emb i)) *
        p4Q2PZ37ABQ2_originalRemotePerronWeight H p b hb B x ∂ν) =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) b hb‖ * Ω b hb B := by
  have hF := p4Q2PZ37ABQ2_originalKernelSection_fourEdge_integral
    H p b hb B (fun _ => 1) continuous_const
  simp only [mul_one] at hF
  have hSame : (∫ A : Cfg, Ω b hb A * K b A B ∂haar) =
      ∫ A : Cfg,
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H 2 (by norm_num) b hb).1 A * K b A B ∂haar := by
    apply integral_congr_ae
    filter_upwards [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_ae_eq_existing
      H 2 (by norm_num) b hb] with A hA
    exact congrArg (fun z : ℝ => z * K b A B) hA
  exact hF.symm.trans (hSame.trans
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_topNorm_mul_eq_integral_kernel
      H 2 (by norm_num) b hb B).symm)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABQ2_originalWeight_eq_halfWeight_mul_vacuum
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABQ2_originalWeight_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABQ2_originalRemotePerronWeight_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABQ2_originalRemotePerronWeight_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABQ2_originalRemotePerronWeight_le_exp
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABQ2_originalRemotePerronWeight_twoSided
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABQ2_originalKernelSection_fourEdge_integral
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABQ2_originalKernelSection_fourEdge_mass
