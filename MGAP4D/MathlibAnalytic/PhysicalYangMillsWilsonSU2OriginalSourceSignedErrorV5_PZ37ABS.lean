import MGAP4D.MathlibAnalytic.RealIntegralRelativeWeightSignedError
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalSourceRemoteCorrectionV5_PZ37ABR
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ABS — actual remote source comparison and signed error budget

The true source-side remote integral S of ABR has no inserted source Perron
factor. Four actual link changes cost exp(24*b), from exp(6*b) per spatial
half-weight link. Integrating all original remote temporal factors preserves
this relative comparison. Together with ABQ2's exp(56*b) comparison for R,
the exact source correction V=S/R has relative comparison exp(80*b).

For a signed continuous four-edge test f, retain the actual anchor S(y).
The original full-kernel section differs from hW(B)*S(y)*integral K4*f by
at most hW(B)*S(y)*(exp(24*b)-1)*integral K4*abs(f). The entire signed test,
including its negative part, is kept. A positive signed margin is stated
only as an explicit conditional criterion, not as an established GI floor.

ABR's physical t*Omega(B) and V=S/R remain in the corrected-density version.
No interacting posterior is replaced, no remote absolute mass is declared
uniform, and no full GI negative-tail, pair-Haar or continuum closure follows.
-/

namespace MGAP4D.MathlibAnalytic
open MeasureTheory
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 1000000

local instance p4Q2PZ37ABS_finTwoFintype : Fintype (Fin 2) := Fin.fintype 2
local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "X" => Fin 4 → G
local notation "μ" => normalizedCompactHaar G
local instance p4Q2PZ37ABS_group : IsTopologicalGroup G := specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ABS_compact : CompactSpace G := specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ABS_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ABS_measurable : MeasurableSpace G :=
  oneSlabHaarL2SpecialUnitaryMeasurableSpace 2
local instance p4Q2PZ37ABS_borel : BorelSpace G := specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ABS_probability : IsProbabilityMeasure μ :=
  normalizedCompactHaar_isProbabilityMeasure G

namespace GroundStatePosteriorJoint
variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local instance p4Q2PZ37ABS_linkDecEq : DecidableEq Link :=
  fun a b => Classical.propDecidable (a = b)
local instance p4Q2PZ37ABS_links : Fintype Link := Fintype.ofFinite _
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "haar" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "hW" => periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight H 2
local notation "K" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2
local notation "Ω" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
  H 2 (by norm_num)

private theorem p4Q2PZ37ABS_halfWeight_oneLink_le
    (b : ℝ) (hb : 0 ≤ b) (A : Cfg) (target : Link) (g h : G) :
    hW b (Function.update A target g) ≤
      Real.exp (6 * b) * hW b (Function.update A target h) := by
  classical
  let Bg : Cfg := Function.update A target g
  let Bh : Cfg := Function.update A target h
  let a : ℝ := periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2 Bg
  let d : ℝ := periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2 Bh
  let theta : ℝ := b / 2
  have hs : |a - d| ≤ 12 := by
    simpa [a, d, Bg, Bh,
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink] using
      (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuousVacuumReplaceLink_sub_abs_le_twelve
        H 2 (by norm_num) A target g h)
  have hreverse : d - a ≤ 12 := by
    have h := (abs_le.mp hs).1
    linarith
  have htheta : 0 ≤ theta := div_nonneg hb (by norm_num)
  have hscaled := mul_le_mul_of_nonneg_left hreverse htheta
  have hlog : -(theta * a) ≤ 6 * b + -(theta * d) := by
    dsimp [theta] at *
    nlinarith [hscaled]
  have he : Real.exp (-(theta * a)) ≤
      Real.exp (6 * b) * Real.exp (-(theta * d)) := by
    calc
      _ ≤ Real.exp (6 * b + -(theta * d)) := Real.exp_le_exp.mpr hlog
      _ = _ := by rw [Real.exp_add]
  change Real.exp (-(theta * a)) ≤
    Real.exp (6 * b) * Real.exp (-(theta * d))
  exact he

private theorem p4Q2PZ37ABS_halfWeight_fourEdge_le
    (b : ℝ) (hb : 0 ≤ b) (p : Plaq) (A B : Cfg)
    (hremote : ∀ e : Link,
      e ∉ Set.range (p4Q2MY_originalPlaquetteFourEdgeEmbedding H p) → A e = B e) :
    hW b A ≤ Real.exp (24 * b) * hW b B := by
  have hstep : ∀ (C : Cfg) (target : Link) (g : G),
      hW b (Function.update C target g) ≤ Real.exp (6 * b) * hW b C := by
    intro C target g
    have hId : Function.update C target (C target) = C := by
      funext i
      by_cases hi : i = target
      · subst i
        simp
      · simp [hi]
    have h := p4Q2PZ37ABS_halfWeight_oneLink_le H b hb C target g (C target)
    rw [hId] at h
    exact h
  have hFour := p4Q2PZ37ABQ_finiteFourCoordinateHarnack
    (ι := Link) (α := G) (hW b) (Real.exp (6 * b)) (Real.exp_nonneg _) hstep
    (p4Q2MY_originalPlaquetteFourEdgeEmbedding H p) A B hremote
  have hc : (Real.exp (6 * b)) ^ 4 = Real.exp (24 * b) := by
    rw [show (24 : ℝ) * b = (6 * b) + (6 * b) + (6 * b) + (6 * b) by ring]
    rw [Real.exp_add, Real.exp_add, Real.exp_add]
    ring
  simpa only [hc] using hFour

variable (p : Plaq)
include p
local notation "emb" => p4Q2MY_originalPlaquetteFourEdgeEmbedding H p
local notation "Remote" => {e : Link // e ∉ Set.range emb}
local notation "ρ" => Measure.pi (fun _ : Remote => μ)
local notation "ν" => Measure.pi (fun _ : Fin 4 => μ)
local notation "assemble" => finiteProductEmbeddingAssemble emb
local notation "S" => p4Q2PZ37ABR_originalRemoteSourceWeight H p
local notation "R" => p4Q2PZ37ABQ2_originalRemotePerronWeight H p
local notation "V" => p4Q2PZ37ABR_originalSourceCorrection H p
local notation "D" => p4Q2PZ37ABR_originalPerronFourEdgeDensity H p
local notation "Kr" => p4Q2PZ37ABQ2_originalRemoteTemporalKernel H p
local notation "K4" => p4Q2PZ37ABO2_originalFourLinkWilsonKernel

private theorem p4Q2PZ37ABS_remote_pos (b : ℝ) (B : Cfg) (r : Remote → G) :
    0 < Kr b B r := by
  unfold p4Q2PZ37ABQ2_originalRemoteTemporalKernel
  apply Finset.prod_pos
  intro e _
  change 0 < Real.exp _
  exact Real.exp_pos _

private theorem p4Q2PZ37ABS_four_continuous (b : ℝ) (B : Cfg) :
    Continuous (fun x : X => K4 b x (fun i => B (emb i))) := by
  change Continuous (fun x : X =>
    ∏ i : Fin 4, specialUnitaryWilsonRelativeKernel 2 b (x i) (B (emb i)))
  exact continuous_finset_prod _ (fun i _ =>
    (continuous_specialUnitaryWilsonRelativeKernel 2 b).comp₂
      (continuous_apply i) continuous_const)

private theorem p4Q2PZ37ABS_four_pos (b : ℝ) (B : Cfg) (x : X) :
    0 < K4 b x (fun i => B (emb i)) := by
  unfold p4Q2PZ37ABO2_originalFourLinkWilsonKernel
  apply Finset.prod_pos
  intro i _
  change 0 < Real.exp _
  exact Real.exp_pos _

/-- The actual source remote integral has a volume-independent relative
factor exp(24*b), with all original remote temporal factors retained. -/
theorem p4Q2PZ37ABS_originalRemoteSourceWeight_le_exp
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (x y : X) :
    S b B x ≤ Real.exp (24 * b) * S b B y := by
  have hcompare (r : Remote → G) :
      hW b (assemble x r) ≤ Real.exp (24 * b) * hW b (assemble y r) := by
    apply p4Q2PZ37ABS_halfWeight_fourEdge_le H b hb p
    intro e he
    have hx := finiteProductEmbeddingAssemble_remote emb x r ⟨e, he⟩
    have hy := finiteProductEmbeddingAssemble_remote emb y r ⟨e, he⟩
    exact hx.trans hy.symm
  have hIntX := p4Q2PZ37ABR_originalRemoteSourceWeight_integrable H p b B x
  have hIntY := p4Q2PZ37ABR_originalRemoteSourceWeight_integrable H p b B y
  change (∫ r : Remote → G, hW b (assemble x r) * Kr b B r ∂ρ) ≤ _
  calc
    _ ≤ ∫ r : Remote → G,
        Real.exp (24 * b) * (hW b (assemble y r) * Kr b B r) ∂ρ := by
      apply integral_mono hIntX (hIntY.const_mul _)
      intro r
      have h := mul_le_mul_of_nonneg_right (hcompare r)
        (p4Q2PZ37ABS_remote_pos H p b B r).le
      simpa only [mul_assoc] using h
    _ = _ := integral_const_mul _ _

/-- Both directions, including every finite H and H=0. This does not assert
an absolute uniform lower bound on S(y). -/
theorem p4Q2PZ37ABS_originalRemoteSourceWeight_twoSided
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (x y : X) :
    Real.exp (-(24 * b)) * S b B y ≤ S b B x ∧
      S b B x ≤ Real.exp (24 * b) * S b B y := by
  constructor
  · have h := mul_le_mul_of_nonneg_left
      (p4Q2PZ37ABS_originalRemoteSourceWeight_le_exp H p b hb B y x)
      (Real.exp_nonneg (-(24 * b)))
    have hc : Real.exp (-(24 * b)) * Real.exp (24 * b) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    simpa only [← mul_assoc, hc, one_mul] using h
  · exact p4Q2PZ37ABS_originalRemoteSourceWeight_le_exp H p b hb B x y

/-- The exact correction V=S/R has its own relative bound exp(80*b).
In particular, it cannot be silently replaced by one. -/
theorem p4Q2PZ37ABS_originalSourceCorrection_le_exp
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (x y : X) :
    V b hb B x ≤ Real.exp (80 * b) * V b hb B y := by
  have hrx := p4Q2PZ37ABQ2_originalRemotePerronWeight_pos H p b hb B x
  have hry := p4Q2PZ37ABQ2_originalRemotePerronWeight_pos H p b hb B y
  have hsy := p4Q2PZ37ABR_originalRemoteSourceWeight_pos H p b B y
  have hs := p4Q2PZ37ABS_originalRemoteSourceWeight_le_exp H p b hb B x y
  have hr := p4Q2PZ37ABQ2_originalRemotePerronWeight_le_exp H p b hb B y x
  have hc : Real.exp (80 * b) = Real.exp (24 * b) * Real.exp (56 * b) := by
    rw [← Real.exp_add]
    congr 1
    ring
  change S b B x / R b hb B x ≤ Real.exp (80 * b) * (S b B y / R b hb B y)
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ hrx hry).mpr
  calc
    _ ≤ (Real.exp (24 * b) * S b B y) * R b hb B y :=
      mul_le_mul_of_nonneg_right hs hry.le
    _ ≤ (Real.exp (24 * b) * S b B y) * (Real.exp (56 * b) * R b hb B x) :=
      mul_le_mul_of_nonneg_left hr (mul_nonneg (Real.exp_nonneg _) hsy.le)
    _ = _ := by rw [hc]; ring

attribute [local irreducible]
  p4Q2MY_originalPlaquetteFourEdgeEmbedding
  finiteProductEmbeddingAssemble

/-- Signed error of the ORIGINAL full one-slab source section relative to
an actual anchored temporal section. The full |f| cost controls cancellation. -/
theorem p4Q2PZ37ABS_originalKernelSection_signed_error
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (y : X) (f : X → ℝ) (hf : Continuous f) :
    |(∫ A : Cfg, K b A B * f (fun i => A (emb i)) ∂haar) -
      hW b B * S b B y * (∫ x : X, K4 b x (fun i => B (emb i)) * f x ∂ν)| ≤
      hW b B * S b B y * (Real.exp (24 * b) - 1) *
        (∫ x : X, K4 b x (fun i => B (emb i)) * |f x| ∂ν) := by
  have hC : 1 ≤ Real.exp (24 * b) := by
    simpa only [Real.exp_zero] using
      (Real.exp_le_exp.mpr (show (0 : ℝ) ≤ 24 * b by positivity))
  have hwB : 0 < hW b B := by
    change 0 < Real.exp _
    exact Real.exp_pos _
  have h := abs_integral_relativeWeight_sub_anchor_le ν
    (fun x : X => K4 b x (fun i => B (emb i))) (S b B) f
    (p4Q2PZ37ABS_four_continuous H p b B)
    (p4Q2PZ37ABR_originalRemoteSourceWeight_continuous H p b B) hf
    (fun x => (p4Q2PZ37ABS_four_pos H p b B x).le)
    (fun x => (p4Q2PZ37ABR_originalRemoteSourceWeight_pos H p b B x).le)
    (Real.exp (24 * b)) hC
    (fun x z => p4Q2PZ37ABS_originalRemoteSourceWeight_le_exp H p b hb B x z) y
  rw [p4Q2PZ37ABR_originalKernelSection_withoutVacuum H p b B f hf]
  calc
    _ = hW b B * |(∫ x : X, K4 b x (fun i => B (emb i)) * S b B x * f x ∂ν) -
        S b B y * (∫ x : X, K4 b x (fun i => B (emb i)) * f x ∂ν)| := by
      rw [← abs_of_pos hwB, ← abs_mul]
      congr 1
      ring
    _ ≤ hW b B * ((Real.exp (24 * b) - 1) * S b B y *
        (∫ x : X, K4 b x (fun i => B (emb i)) * |f x| ∂ν)) :=
      mul_le_mul_of_nonneg_left h hwB.le
    _ = _ := by ring

/-- Actual signed lower bound; no positive-margin premise is hidden. -/
theorem p4Q2PZ37ABS_originalKernelSection_signed_lower
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (y : X) (f : X → ℝ) (hf : Continuous f) :
    hW b B * S b B y *
      ((∫ x : X, K4 b x (fun i => B (emb i)) * f x ∂ν) -
        (Real.exp (24 * b) - 1) *
          (∫ x : X, K4 b x (fun i => B (emb i)) * |f x| ∂ν)) ≤
      ∫ A : Cfg, K b A B * f (fun i => A (emb i)) ∂haar := by
  have h := (abs_le.mp
    (p4Q2PZ37ABS_originalKernelSection_signed_error H p b hb B y f hf)).1
  nlinarith

/-- A positive original signed section follows only after an explicit
signed temporal margin dominates the entire relative-weight error budget. -/
theorem p4Q2PZ37ABS_originalKernelSection_pos_of_margin
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (y : X) (f : X → ℝ) (hf : Continuous f)
    (hmargin : (Real.exp (24 * b) - 1) *
      (∫ x : X, K4 b x (fun i => B (emb i)) * |f x| ∂ν) <
        ∫ x : X, K4 b x (fun i => B (emb i)) * f x ∂ν) :
    0 < ∫ A : Cfg, K b A B * f (fun i => A (emb i)) ∂haar := by
  have hwB : 0 < hW b B := by
    change 0 < Real.exp _
    exact Real.exp_pos _
  exact lt_of_lt_of_le
    (mul_pos (mul_pos hwB (p4Q2PZ37ABR_originalRemoteSourceWeight_pos H p b B y))
      (sub_pos.mpr hmargin))
    (p4Q2PZ37ABS_originalKernelSection_signed_lower H p b hb B y f hf)

/-- The same signed error in the exact corrected Perron representation.
The original t*Omega factor, true density D and actual V=S/R are retained. -/
theorem p4Q2PZ37ABS_correctedPerron_signed_error
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (y : X) (f : X → ℝ) (hf : Continuous f) :
    |(‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) b hb‖ * Ω b hb B) *
          (∫ x : X, D b hb B x * V b hb B x * f x ∂ν) -
      hW b B * S b B y * (∫ x : X, K4 b x (fun i => B (emb i)) * f x ∂ν)| ≤
      hW b B * S b B y * (Real.exp (24 * b) - 1) *
        (∫ x : X, K4 b x (fun i => B (emb i)) * |f x| ∂ν) := by
  rw [← p4Q2PZ37ABR_originalKernelSection_correctedPerronDensity H p b hb B f hf]
  exact p4Q2PZ37ABS_originalKernelSection_signed_error H p b hb B y f hf

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABS_originalRemoteSourceWeight_le_exp
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABS_originalRemoteSourceWeight_twoSided
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABS_originalSourceCorrection_le_exp
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABS_originalKernelSection_signed_error
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABS_originalKernelSection_signed_lower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABS_originalKernelSection_pos_of_margin
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABS_correctedPerron_signed_error
