import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTouchingLinkGIObstructionV5_MO
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabRightTargetKernelHarnack
import Mathlib.Tactic

/-!
# P4-Q2-MP — quantitative one-link sensitivity of the ACTUAL original
# signed interacting Wilson posterior receiver Riesz density

A geometric one-link locality identity for Wilson *observables* (MO)
does NOT imply that the true two-interacting-posterior signed response
of a distant plaquette is zero. The receiver integrates the original
Wilson one-slab kernel against the genuine signed posterior density
contrast and its positive joint Perron half-density (JH).

Here we instead control the actual RIESZ REPRESENTING DENSITY of that
same receiver under a link replacement in its **source configuration**
A, without moving the frozen right context z or changing either genuine
posterior. Symmetry of the *original* Wilson kernel transports the
already proved right-link Harnack factor exp(8b) to its left side.

Because 0 < K_b <= 1, that Harnack comparison gives the nontrivial
pointwise modulus
  |K_b(A_g,B)-K_b(A_h,B)| <= exp(8b)-1.
Combining the SAME original interacting-posterior contrast
  |p_0(g)-p_pi(g)| <= exp(16b)-exp(-16b)
with LV's true normalized joint-half-density one-link ratio
  s(z)/s(z.left,z.right[e:=g]) <= exp(8b),
gives a uniform original *scaled signed* JH fiber-kernel difference
  <= (exp(8b)-1) * E_b,
where E_b = exp(8b)*(exp(16b)-exp(-16b)).

Integrating over the ORIGINAL normalized SU(2) reference Haar yields
the same bound for the actual original interacting Wilson Riesz
representer, multiplied by its true scalar s(z). The compensated
signed receiver density -s(z) r_{e,z}(A) represents literally
||T||*GI_{e,z}, using LW's exact positive transfer normalization
identity; it has the same one-link oscillation bound.

The bound is genuinely independent of spatial H and the source-side
link, physical receiver link, and context. It is a LOCAL OSCILLATION
bound of the real signed receiver's Riesz density, *not* a spatial
separation decay estimate, not a conditional-covariance cancellation,
not a uniform lower coercivity floor and not a new independent-Haar
posterior or artificial gauge-invariant source.

In particular this does not identify the source-side coordinate
replacement with a Gauss-law physical source: the Riesz density is
the exact original bounded-functional representation on Haar-L².
Endpoint fine coupling, arbitrary Krylov source separation, H1-C3
and the continuum Yang–Mills mass gap are still OPEN.

No sorry, admit, axiom, invented rank, Dobrushin, or posterior change.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2MP_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2MP_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2MP_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2MP_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2MP_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section Frozen
variable (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "haar" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "nu" => normalizedCompactHaar Gauge
local notation "s" => continuousJointSqrtDensity H 2 (by norm_num) b hb
local notation "K" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 b
local notation "delta" => p4Q2GB_originalWilsonPosteriorLeftDensityContrast H b hb
local notation "E" => p4Q2LW_originalHarnackContrastScale b
local notation "R" => p4Q2JH_originalFiberRepresenter H b hb
local notation "F" => p4Q2JH_originalFiberKernel H b hb
local notation "Q" => p4Q2LW_originalTransferCompensatedGIResponse H b hb
local notation "L" => ContinuousMap.toLp 2 haar ℝ

/-- Genuine SU(2) complete one-slab Wilson kernel Harnack comparison on
the LEFT boundary, via exact kernel symmetry and the already proved
right-link Harnack. This is not a new transfer or a changed measure. -/
theorem p4Q2MP_originalWilsonKernel_leftLink_harnack
    (A B : Cfg) (target : Link) (g h : Gauge) :
    K (Function.update A target g) B ≤
      Real.exp (8*b) * K (Function.update A target h) B := by
  calc
    K (Function.update A target g) B =
        K B (Function.update A target g) :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_symmetric
        H 2 (by norm_num) b hb (Function.update A target g) B
    _ ≤ Real.exp (8*b) * K B (Function.update A target h) :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_update_right_le_exp_eight_mul_update_right
        H 2 (by norm_num) b hb B A target g h
    _ = Real.exp (8*b) * K (Function.update A target h) B := by
      rw [← periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_symmetric
        H 2 (by norm_num) b hb (Function.update A target h) B]

/-- Pointwise ORIGINAL Wilson kernel difference for any left source-side
single-link variation. The sharp H-independent oscillation envelope
vanishes at beta=0: it uses BOTH positivity and the real Harnack ratio,
not the coarse universal |K|<=1 alone. -/
theorem p4Q2MP_originalWilsonKernel_leftLink_abs_sub_le
    (A B : Cfg) (target : Link) (g h : Gauge) :
    |K (Function.update A target g) B -
      K (Function.update A target h) B| ≤
      Real.exp (8*b) - 1 := by
  let c : ℝ := Real.exp (8*b)
  let kg : ℝ := K (Function.update A target g) B
  let kh : ℝ := K (Function.update A target h) B
  have hNonneg : 0 ≤ 8*b := mul_nonneg (by norm_num) hb
  have hc : 1 ≤ c := by
    change 1 ≤ Real.exp (8*b)
    simpa using (Real.exp_le_exp.mpr hNonneg : Real.exp 0 ≤ Real.exp (8*b))
  have hcm : 0 ≤ c-1 := sub_nonneg.mpr hc
  have hg : kg ≤ c*kh :=
    p4Q2MP_originalWilsonKernel_leftLink_harnack H b hb A B target g h
  have hh : kh ≤ c*kg :=
    p4Q2MP_originalWilsonKernel_leftLink_harnack H b hb A B target h g
  have hkg : kg ≤ 1 := (abs_le.mp
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
      H 2 (by norm_num) b hb (Function.update A target g) B)).2
  have hkh : kh ≤ 1 := (abs_le.mp
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
      H 2 (by norm_num) b hb (Function.update A target h) B)).2
  have hForward : kg-kh ≤ c-1 := by
    calc
      kg-kh ≤ (c-1)*kh := by nlinarith [hg]
      _ ≤ (c-1)*1 := mul_le_mul_of_nonneg_left hkh hcm
      _ = c-1 := mul_one _
  have hReverse : kh-kg ≤ c-1 := by
    calc
      kh-kg ≤ (c-1)*kg := by nlinarith [hh]
      _ ≤ (c-1)*1 := mul_le_mul_of_nonneg_left hkg hcm
      _ = c-1 := mul_one _
  change |kg-kh| ≤ c-1
  rw [abs_le]
  constructor <;> linarith

/-- The true original JH *signed* fiber integrand under a source-side
one-link replacement has a pointwise oscillation bounded by
  (exp(8b)-1) E_b,
INCLUDING the original TWO interacting posterior density difference
and the SAME true joint Perron half-density. Frozen receiver
context z and posterior fiber e are held fixed. -/
theorem p4Q2MP_originalScaledSignedFiberKernel_leftLink_abs_sub_le
    (e target : Link) (z : Cfg × Cfg)
    (A : Cfg) (g h xi : Gauge) :
    |s z * F e z (xi, Function.update A target g) -
      s z * F e z (xi, Function.update A target h)| ≤
        (Real.exp (8*b)-1)*E := by
  let M : ℝ := Real.exp (8*b)
  let D : ℝ := p4Q2LS_originalPosteriorContrastEnvelope b
  let Bg : Cfg := Function.update z.2 e xi
  let Ag : Cfg := Function.update A target g
  let Ah : Cfg := Function.update A target h
  have hM : 0 ≤ M-1 := by
    apply sub_nonneg.mpr
    change 1 ≤ Real.exp (8*b)
    simpa using (Real.exp_le_exp.mpr
      (mul_nonneg (by norm_num) hb) : Real.exp 0 ≤ Real.exp (8*b))
  have hKm :
      |K Ag Bg - K Ah Bg| ≤ M-1 :=
    p4Q2MP_originalWilsonKernel_leftLink_abs_sub_le
      H b hb A Bg target g h
  have hRpos :
      0 < s z * (s (z.1, Bg))⁻¹ :=
    mul_pos
      (continuousJointSqrtDensity_pos H 2 (by norm_num) b hb z)
      (inv_pos.mpr
        (continuousJointSqrtDensity_pos H 2 (by norm_num) b hb (z.1, Bg)))
  have hRm :
      |s z * (s (z.1, Bg))⁻¹| ≤ M := by
    have h :=
      p4Q2LV_originalJointHalfDensityRatio_pointwise_le_exp_eight
        H b hb e z xi
    change s z * (s (z.1, Bg))⁻¹ ≤ M at h
    simpa only [abs_of_pos hRpos] using h
  have hDm : |delta z.2 e xi| ≤ D :=
    p4Q2JL_originalPosteriorContrast_abs_le H b hb z.2 e xi
  have hDpos : 0 ≤ D :=
    p4Q2LS_originalPosteriorContrastEnvelope_nonneg b hb
  have hPair :
      |K Ag Bg - K Ah Bg| *
        |s z * (s (z.1, Bg))⁻¹| ≤ (M-1)*M :=
    mul_le_mul hKm hRm (abs_nonneg _) hM
  have hAll :
      (|K Ag Bg-K Ah Bg| *
        |s z * (s (z.1, Bg))⁻¹|) *
        |delta z.2 e xi| ≤ ((M-1)*M)*D :=
    mul_le_mul hPair hDm (abs_nonneg _) (mul_nonneg hM (Real.exp_pos _).le)
  change |s z*(K Ag Bg*(s (z.1, Bg))⁻¹*delta z.2 e xi) -
    s z*(K Ah Bg*(s (z.1, Bg))⁻¹*delta z.2 e xi)| ≤
      (M-1)*E
  calc
    |s z*(K Ag Bg*(s (z.1, Bg))⁻¹*delta z.2 e xi) -
      s z*(K Ah Bg*(s (z.1, Bg))⁻¹*delta z.2 e xi)| =
      (|K Ag Bg-K Ah Bg| *
        |s z * (s (z.1, Bg))⁻¹|) *
        |delta z.2 e xi| := by
          have hfactor :
            s z*(K Ag Bg*(s (z.1, Bg))⁻¹*delta z.2 e xi) -
              s z*(K Ah Bg*(s (z.1, Bg))⁻¹*delta z.2 e xi) =
              ((K Ag Bg-K Ah Bg)*(s z*(s (z.1, Bg))⁻¹))*
                delta z.2 e xi := by ring
          rw [hfactor, abs_mul, abs_mul]
    _ ≤ ((M-1)*M)*D := hAll
    _ = (M-1)*E := by
      dsimp [E, M, D, p4Q2LW_originalHarnackContrastScale]
      ring

/-- SU(2) Haar integration of the very same original Wilson signed
fiber kernel preserves the physical one-link oscillation bound.
It is uniform in finite volume but does NOT assert covariance
decay with spatial separation from the receiver. -/
theorem p4Q2MP_originalScaledSignedFiberRepresenter_leftLink_abs_sub_le
    (e target : Link) (z : Cfg × Cfg)
    (A : Cfg) (g h : Gauge) :
    |s z * R e z (Function.update A target g) -
      s z * R e z (Function.update A target h)| ≤
      (Real.exp (8*b)-1)*E := by
  let Ag : Cfg := Function.update A target g
  let Ah : Cfg := Function.update A target h
  let k := F e z
  let r := R e z
  let C : ℝ := (Real.exp (8*b)-1)*E
  have hIg : Integrable (fun xi : Gauge => k (xi, Ag)) nu := by
    have hc : Continuous (fun xi : Gauge => k (xi,Ag)) :=
      k.continuous.comp (continuous_id.prodMk continuous_const)
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hIh : Integrable (fun xi : Gauge => k (xi, Ah)) nu := by
    have hc : Continuous (fun xi : Gauge => k (xi,Ah)) :=
      k.continuous.comp (continuous_id.prodMk continuous_const)
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hIntegral :
      s z * r Ag - s z * r Ah =
        ∫ xi : Gauge,
          (s z * k (xi, Ag) - s z * k (xi, Ah)) ∂nu := by
    rw [p4Q2JH_originalFiberRepresenter_apply H b hb e z Ag,
      p4Q2JH_originalFiberRepresenter_apply H b hb e z Ah]
    rw [integral_sub (hIg.const_mul _) (hIh.const_mul _),
      integral_const_mul, integral_const_mul]
  have hBound :
      ‖∫ xi : Gauge,
          (s z * k (xi, Ag) - s z * k (xi, Ah)) ∂nu‖ ≤
        C * nu.real Set.univ := by
    apply norm_integral_le_of_norm_le_const
    filter_upwards with xi
    rw [Real.norm_eq_abs]
    exact p4Q2MP_originalScaledSignedFiberKernel_leftLink_abs_sub_le
      H b hb e target z A g h xi
  have hUniv : nu.real Set.univ = 1 := by simp [measureReal_def]
  rw [hIntegral, ← Real.norm_eq_abs]
  simpa only [hUniv, mul_one] using hBound

/-- This is precisely the ORIGINAL physical signed GI receiver Riesz
density after LW's already verified transfer-norm compensation, and
not a new detector: -s(z) times the existing original JH representer. -/
noncomputable def p4Q2MP_originalCompensatedSignedReceiverRieszDensity
    (e : Link) (z : Cfg × Cfg) : C(Cfg, ℝ) :=
  (-(s z)) • R e z

/-- Exact Hilbert-functional identity for the *same* original
two-interacting-Wilson-posterior signed receiver multiplied by ||T||.
No fictitious rank, auxiliary posterior or gauge source is introduced. -/
theorem p4Q2MP_originalCompensatedSignedReceiver_eq_RieszDensity
    (e : Link) (z : Cfg × Cfg)
    (u : Lp ℝ 2 haar) :
    Q e z u =
      inner ℝ
        (L (p4Q2MP_originalCompensatedSignedReceiverRieszDensity
          H b hb e z)) u := by
  rw [p4Q2LW_originalCompensatedGI_eq_originalRiesz]
  change (-(s z))*inner ℝ (L (R e z)) u =
    inner ℝ (L ((-(s z)) • R e z)) u
  rw [map_smul, real_inner_smul_left]
  rfl

/-- The ORIGINAL compensated interacting-posterior signed GI Riesz
density has H-independent one-link source-side oscillation
  (exp(8b)-1) * E_b.
This bounds the exact receiver kernel, not arbitrary posterior
correlations or a positive physical source-coercivity floor. -/
theorem p4Q2MP_originalCompensatedSignedReceiver_oneLinkOscillation
    (e target : Link) (z : Cfg × Cfg)
    (A : Cfg) (g h : Gauge) :
    |p4Q2MP_originalCompensatedSignedReceiverRieszDensity H b hb e z
        (Function.update A target g) -
      p4Q2MP_originalCompensatedSignedReceiverRieszDensity H b hb e z
        (Function.update A target h)| ≤
      (Real.exp (8*b)-1)*E := by
  have h :=
    p4Q2MP_originalScaledSignedFiberRepresenter_leftLink_abs_sub_le
      H b hb e target z A g h
  change |(-(s z))*R e z (Function.update A target g) -
    (-(s z))*R e z (Function.update A target h)| ≤ _
  have heq :
      (-(s z))*R e z (Function.update A target g) -
        (-(s z))*R e z (Function.update A target h) =
      -(s z*R e z (Function.update A target g) -
        s z*R e z (Function.update A target h)) := by ring
  rw [heq, abs_neg]
  exact h

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MP_originalWilsonKernel_leftLink_harnack
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MP_originalWilsonKernel_leftLink_abs_sub_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MP_originalScaledSignedFiberKernel_leftLink_abs_sub_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MP_originalScaledSignedFiberRepresenter_leftLink_abs_sub_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MP_originalCompensatedSignedReceiver_eq_RieszDensity
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MP_originalCompensatedSignedReceiver_oneLinkOscillation
