import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalLocalGradeBinomialV5_PZ37ART
import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonKernelPartialBound
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalTransferUniformVolumeVanishingV5_PZ37AIU
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ARU — local Taylor truncation of the original interacting slab

The finite Taylor kernel already constructed for one genuine SU(2) link
has a uniform absolute tail bound. Multiply the finite Taylor kernels over
the literal original spatial links and retain BOTH original spatial
halfweights. The pointwise uniform error is at most the actual link count
times the local scalar tail. This is an unnormalized kernel estimate,
not a uniform normalized operator estimate or a spectral support grading.
-/
namespace MGAP4D.MathlibAnalytic
open Filter NormedSpace
open scoped Topology BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 50000

private def p4Q2PZ37ARU_poly (z : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, z^j/(Nat.factorial j : ℝ)

private theorem p4Q2PZ37ARU_poly_tendsto (z : ℝ) :
    Tendsto (p4Q2PZ37ARU_poly z) atTop (𝓝 (Real.exp z)) := by
  unfold p4Q2PZ37ARU_poly
  apply HasSum.tendsto_sum_nat
  rw [Real.exp_eq_exp_ℝ]
  exact expSeries_div_hasSum_exp z

private theorem p4Q2PZ37ARU_poly_tail_aux (z b : ℝ) (hz : |z| ≤ b) (n m : ℕ) :
    |p4Q2PZ37ARU_poly z (m+n)-p4Q2PZ37ARU_poly z n| ≤
      p4Q2PZ37ARU_poly b (m+n)-p4Q2PZ37ARU_poly b n := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hterm :
          |z^(m+n)/(Nat.factorial (m+n) : ℝ)| ≤
            b^(m+n)/(Nat.factorial (m+n) : ℝ) := by
        rw [abs_div, abs_pow, abs_of_nonneg (by positivity : 0 ≤ (Nat.factorial (m+n) : ℝ))]
        exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg z) hz _) (by positivity)
      have hstep (x : ℝ) : p4Q2PZ37ARU_poly x (m.succ+n) =
          p4Q2PZ37ARU_poly x (m+n)+x^(m+n)/(Nat.factorial (m+n) : ℝ) := by
        rw [Nat.succ_add]
        exact Finset.sum_range_succ _ _
      rw [hstep z,hstep b]
      calc
        _ = |(p4Q2PZ37ARU_poly z (m+n)-p4Q2PZ37ARU_poly z n)+
            z^(m+n)/(Nat.factorial (m+n) : ℝ)| := by congr 1; ring
        _ ≤ |p4Q2PZ37ARU_poly z (m+n)-p4Q2PZ37ARU_poly z n|+
            |z^(m+n)/(Nat.factorial (m+n) : ℝ)| := abs_add_le _ _
        _ ≤ _ := by linarith only [ih,hterm]

private theorem p4Q2PZ37ARU_scalar_tail (z b : ℝ) (hz : |z| ≤ b) (n : ℕ) :
    |Real.exp z-p4Q2PZ37ARU_poly z n| ≤ Real.exp b-p4Q2PZ37ARU_poly b n := by
  have hzlim := (tendsto_add_atTop_iff_nat (f := p4Q2PZ37ARU_poly z) n).2
    (p4Q2PZ37ARU_poly_tendsto z)
  have hblim := (tendsto_add_atTop_iff_nat (f := p4Q2PZ37ARU_poly b) n).2
    (p4Q2PZ37ARU_poly_tendsto b)
  exact le_of_tendsto_of_tendsto'
    (hzlim.sub tendsto_const_nhds).abs (hblim.sub tendsto_const_nhds)
    (fun m => p4Q2PZ37ARU_poly_tail_aux z b hz n m)

private theorem p4Q2PZ37ARU_listProd_abs
    {I : Type} (f : I → ℝ) (hf : ∀ i, |f i| ≤ 1) (s : List I) :
    |(s.map f).prod| ≤ 1 := by
  induction s with
  | nil => simp
  | cons i s ih =>
      simp only [List.map_cons,List.prod_cons,abs_mul]
      exact (mul_le_mul (hf i) ih (abs_nonneg _) (by norm_num)).trans_eq (one_mul 1)

private theorem p4Q2PZ37ARU_listProd_error
    {I : Type} (f g : I → ℝ) (e : ℝ)
    (hf : ∀ i, |f i| ≤ 1) (hg : ∀ i, |g i| ≤ 1)
    (he : ∀ i, |f i-g i| ≤ e) (s : List I) :
    |(s.map f).prod-(s.map g).prod| ≤ (s.length : ℝ)*e := by
  induction s with
  | nil => simp
  | cons i s ih =>
      have hp := p4Q2PZ37ARU_listProd_abs g hg s
      simp only [List.map_cons,List.prod_cons,List.length_cons,Nat.cast_succ]
      calc
        _ = |f i*((s.map f).prod-(s.map g).prod)+(f i-g i)*(s.map g).prod| := by congr 1; ring
        _ ≤ |f i*((s.map f).prod-(s.map g).prod)|+|(f i-g i)*(s.map g).prod| := abs_add_le _ _
        _ ≤ (s.length : ℝ)*e+e := by
          rw [abs_mul,abs_mul]
          have h1 := mul_le_mul_of_nonneg_right (hf i) (abs_nonneg ((s.map f).prod-(s.map g).prod))
          have h2 := mul_le_mul_of_nonneg_left hp (abs_nonneg (f i-g i))
          simp only [one_mul] at h1
          simp only [mul_one] at h2
          exact add_le_add (h1.trans ih) (h2.trans (he i))
        _ = _ := by ring

/-- Exact scalar tail, measured against the positive exponential series. -/
def p4Q2PZ37ARU_tail (beta : ℝ) (degree : ℕ) : ℝ :=
  Real.exp (-beta)*(Real.exp beta-p4Q2PZ37ARU_poly beta (degree+1))

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARU_tail

theorem p4Q2PZ37ARU_tail_nonneg (beta : ℝ) (hb : 0 ≤ beta) (degree : ℕ) :
    0 ≤ p4Q2PZ37ARU_tail beta degree := by
  unfold p4Q2PZ37ARU_tail p4Q2PZ37ARU_poly
  apply mul_nonneg (Real.exp_nonneg _)
  exact sub_nonneg.mpr (Real.sum_le_exp_of_nonneg hb _)

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARU_tail_nonneg

theorem p4Q2PZ37ARU_tail_tendsto_zero (beta : ℝ) :
    Tendsto (p4Q2PZ37ARU_tail beta) atTop (𝓝 0) := by
  have h := (tendsto_add_atTop_iff_nat (f := p4Q2PZ37ARU_poly beta) 1).2
    (p4Q2PZ37ARU_poly_tendsto beta)
  have hd : Tendsto (fun n => Real.exp beta-p4Q2PZ37ARU_poly beta (n+1)) atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℕ => Real.exp beta) atTop (𝓝 (Real.exp beta)) :=
      tendsto_const_nhds
    simpa only [sub_self] using hc.sub h
  simpa only [p4Q2PZ37ARU_tail,mul_zero] using hd.const_mul (Real.exp (-beta))

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARU_tail_tendsto_zero

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration
local notation "Tr" => specialUnitaryNormalizedTraceRelativeKernel
local notation "K" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
local notation "KC" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
local notation "W" => periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight
local notation "L" => periodicHypercubicEvenSpatialSliceLinkList
local notation "k" => specialUnitaryWilsonRelativeKernel
local notation "kp" => specialUnitaryWilsonRelativeKernelPartial
local notation "E" => p4Q2PZ37ARU_tail

theorem p4Q2PZ37ARU_local_tail_bound
    (beta : ℝ) (hb : 0 ≤ beta) (degree : ℕ) (g h : G) :
    |k 2 beta g h-kp 2 beta degree g h| ≤ E beta degree := by
  rw [specialUnitaryWilsonRelativeKernel_eq_trace]
  unfold specialUnitaryWilsonRelativeKernelPartial p4Q2PZ37ARU_tail
  rw [RealHilbertKernelFeature.exponentialPartialKernel_eq_sum,← mul_sub,abs_mul,Real.abs_exp]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
  have hz : |beta*Tr 2 g h| ≤ beta := by
    rw [abs_mul,abs_of_nonneg hb]
    exact (mul_le_mul_of_nonneg_left
      (specialUnitaryNormalizedTraceRelativeKernel_abs_le_one (by decide : 0 < (2:ℕ)) g h) hb).trans_eq (mul_one _)
  exact p4Q2PZ37ARU_scalar_tail _ _ hz _

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARU_local_tail_bound

/-- The actual spatial halfweights are retained exactly. -/
def p4Q2PZ37ARU_partialSlab
    (H : ℕ) (beta : ℝ) (degree : ℕ) (A B : Cfg H 2) : ℝ :=
  W H 2 beta A*((L H).map fun e => kp 2 beta degree (A e) (B e)).prod*W H 2 beta B

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARU_partialSlab

private theorem p4Q2PZ37ARU_kernel_abs_le_one
    (beta : ℝ) (hb : 0 ≤ beta) (g h : G) :
    |k 2 beta g h| ≤ 1 := by
  rw [specialUnitaryWilsonRelativeKernel_eq_trace,abs_mul,Real.abs_exp,Real.abs_exp,← Real.exp_add]
  apply Real.exp_le_one_iff.mpr
  have ht := (le_abs_self (Tr 2 g h)).trans
    (specialUnitaryNormalizedTraceRelativeKernel_abs_le_one (by decide : 0 < (2:ℕ)) g h)
  linarith only [mul_le_mul_of_nonneg_left ht hb]

/-- The genuine interacting slab has an explicit uniform absolute truncation
error. No spatial interaction is removed or treated as independent. -/
theorem p4Q2PZ37ARU_slab_tail_bound
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta) (degree : ℕ) (A B : Cfg H 2) :
    |K H 2 beta A B-p4Q2PZ37ARU_partialSlab H beta degree A B| ≤
      ((L H).length : ℝ)*E beta degree := by
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel p4Q2PZ37ARU_partialSlab
  let f := fun e : PeriodicHypercubicEvenSpatialSliceLink H => k 2 beta (A e) (B e)
  let g := fun e : PeriodicHypercubicEvenSpatialSliceLink H => kp 2 beta degree (A e) (B e)
  have hprod := p4Q2PZ37ARU_listProd_error f g (E beta degree)
    (fun e => p4Q2PZ37ARU_kernel_abs_le_one beta hb (A e) (B e))
    (fun e => specialUnitaryWilsonRelativeKernelPartial_abs_le_one (by decide : 0 < (2:ℕ)) beta hb degree (A e) (B e))
    (fun e => p4Q2PZ37ARU_local_tail_bound beta hb degree (A e) (B e)) (L H)
  have hWA : |W H 2 beta A| ≤ 1 := by
    rw [abs_of_pos (periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight_pos H 2 beta A)]
    exact GroundStatePosteriorJoint.p4Q2PZ37AIU_originalSpatialHalfweight_le_one H beta hb A
  have hWB : |W H 2 beta B| ≤ 1 := by
    rw [abs_of_pos (periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight_pos H 2 beta B)]
    exact GroundStatePosteriorJoint.p4Q2PZ37AIU_originalSpatialHalfweight_le_one H beta hb B
  change |W H 2 beta A*((L H).map f).prod*W H 2 beta B-
    W H 2 beta A*((L H).map g).prod*W H 2 beta B| ≤ _
  calc
    _ = |W H 2 beta A*(((L H).map f).prod-((L H).map g).prod)*W H 2 beta B| := by congr 1; ring
    _ ≤ |((L H).map f).prod-((L H).map g).prod| := by
      rw [abs_mul,abs_mul]
      have h1 := mul_le_mul_of_nonneg_right hWA
        (abs_nonneg (((L H).map f).prod-((L H).map g).prod))
      have h2 := mul_le_mul_of_nonneg_left hWB
        (mul_nonneg (abs_nonneg (W H 2 beta A)) (abs_nonneg (((L H).map f).prod-((L H).map g).prod)))
      simp only [one_mul] at h1
      simp only [mul_one] at h2
      exact h2.trans h1
    _ ≤ _ := hprod

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARU_slab_tail_bound

/-- One common degree for ALL boundary configurations at a fixed true volume. -/
theorem p4Q2PZ37ARU_exists_uniform_slab_degree
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta) (r : ℝ) (hr : 0 < r) :
    ∃ d : ℕ, ∀ n : ℕ, d ≤ n → ∀ A B : Cfg H 2,
      |K H 2 beta A B-p4Q2PZ37ARU_partialSlab H beta n A B| < r := by
  have h := p4Q2PZ37ARU_tail_tendsto_zero beta
  have hl : Tendsto (fun n => ((L H).length : ℝ)*E beta n) atTop (𝓝 0) := by
    simpa only [mul_zero] using h.const_mul ((L H).length : ℝ)
  obtain ⟨d,hd⟩ := eventually_atTop.1 ((tendsto_order.mp hl).2 r hr)
  exact ⟨d,fun n hn A B => (p4Q2PZ37ARU_slab_tail_bound H beta hb n A B).trans_lt (hd n hn)⟩

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARU_exists_uniform_slab_degree

end
end MGAP4D.MathlibAnalytic
