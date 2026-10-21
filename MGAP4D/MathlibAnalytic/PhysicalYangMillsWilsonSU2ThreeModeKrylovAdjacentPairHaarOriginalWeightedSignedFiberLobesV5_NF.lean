import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPosteriorSignedLobeMassV5_NE
import Mathlib.Tactic

/-!
# P4-Q2-NF — ORIGINAL signed Wilson–Perron receiver: weighted lobe separation

ND/NE proved that the two genuinely interacting original normalized
SU(2) Wilson posterior rows are distinct with balanced strictly positive
Haar signed-lobe masses for EVERY beta>0, finite H, physical link e
and physical right-boundary environment.

That density contrast is then passed through the ACTUAL original
complete Wilson kernel and the ACTUAL Perron joint half-density in the
JH continuous Riesz fiber, not an independent-Haar posterior.

NF proves the following at EVERY beta>0 and for EACH original
physical source configuration A and two-boundary context z:

1. The positive Haar mass of JH's ORIGINAL weighted fiber is strictly
   positive.
2. The negative Haar mass of that SAME weighted fiber is strictly
   positive.
3. The genuine JH signed Riesz representer is EXACTLY the difference
   of these two positive weighted masses.
4. The integral of absolute JH fiber strength equals their sum.
   Consequently the signed representer obeys a STRICT triangle
   inequality: some cancellation always happens at beta>0.
5. MQ's ORIGINAL full Wilson kernel is positive and multiplies the
   ACTUAL original local signed two-posterior receiver score:
       K_b(A,z.right) * Psi_(H,b,e,z)(A) = P(A)-N(A).
   The physical receiver score vanishes at A IFF the two positive
   weighted masses BALANCE EXACTLY at that A.

**This is a substantive obstruction refinement**: the signed
receiver's potential zero is due to exact weighted cancellation, NEVER
to absence of signed mass on either side for beta>0.  Neither
sign-changing posterior densities nor nonzero weighted lobe masses
alone prove nonconstant Psi or nonzero GI covariance. We do not claim
those, H1-C3, or continuum 4D Yang–Mills mass gap.

The true original two interacting posterior laws, SU(2) Wilson
interaction, Gauss-law physical source, and Perron half-density are
preserved literally; no artificial detector, substituted conditional
posterior, Dobrushin, rank hypothesis, sorry or new axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2NF_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2NF_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2NF_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2NF_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2NF_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2NF_openPosHaar :
    Measure.IsOpenPosMeasure
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  dsimp [normalizedCompactHaar]
  infer_instance

namespace GroundStatePosteriorJoint

private theorem p4Q2NF_real_signed_parts (x : ℝ) :
    max x 0 - max (-x) 0 = x ∧
      max x 0 + max (-x) 0 = |x| := by
  rcases le_total x 0 with h | h
  · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h), abs_of_nonpos h]
    constructor <;> ring
  · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), abs_of_nonneg h]
    constructor <;> ring

section OriginalWeightedSignedFiber
variable (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "mu" => normalizedCompactHaar Gauge
local notation "K" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 b
local notation "s" => continuousJointSqrtDensity H 2 (by norm_num) b hb
local notation "D" => p4Q2GB_originalWilsonPosteriorLeftDensityContrast H b hb
local notation "k" => p4Q2JH_originalFiberKernel H b hb
local notation "r" => p4Q2JH_originalFiberRepresenter H b hb
local notation "PsiC" => p4Q2MU_originalSignedWilsonScoreContinuous H b hb
include hb

/-- The positive lobe of the EXACT original JH Wilson–Perron signed
physical fiber, with no new detector or posterior probability law. -/
noncomputable def p4Q2NF_originalPhysicalWeightedPositiveLobeMass
    (e : Link) (z : Cfg × Cfg) (A : Cfg) : ℝ :=
  ∫ g : Gauge, max (k e z (g,A)) 0 ∂mu

/-- The negative lobe of that SAME original JH Wilson–Perron
signed physical fiber. -/
noncomputable def p4Q2NF_originalPhysicalWeightedNegativeLobeMass
    (e : Link) (z : Cfg × Cfg) (A : Cfg) : ℝ :=
  ∫ g : Gauge, max (-(k e z (g,A))) 0 ∂mu

local notation "P" => p4Q2NF_originalPhysicalWeightedPositiveLobeMass H b hb
local notation "N" => p4Q2NF_originalPhysicalWeightedNegativeLobeMass H b hb

private theorem p4Q2NF_originalFiberContinuous
    (e : Link) (z : Cfg × Cfg) (A : Cfg) :
    Continuous (fun g : Gauge => k e z (g,A)) :=
  (k e z).continuous.comp (continuous_id.prodMk continuous_const)

private theorem p4Q2NF_originalFiberPositiveLobe_integrable
    (e : Link) (z : Cfg × Cfg) (A : Cfg) :
    Integrable (fun g : Gauge => max (k e z (g,A)) 0) mu :=
  ((p4Q2NF_originalFiberContinuous H b hb e z A).max
    continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

private theorem p4Q2NF_originalFiberNegativeLobe_integrable
    (e : Link) (z : Cfg × Cfg) (A : Cfg) :
    Integrable (fun g : Gauge => max (-(k e z (g,A))) 0) mu :=
  (((p4Q2NF_originalFiberContinuous H b hb e z A).neg).max
    continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- At every b>0 and EVERY frozen authentic source A, the positive
part of the ACTUAL original two-posterior Wilson–Perron signed
Riesz fiber carries strictly POSITIVE Haar mass. -/
theorem p4Q2NF_originalPhysicalWeightedPositiveLobeMass_pos
    (bpos : 0 < b) (e : Link) (z : Cfg × Cfg) (A : Cfg) :
    0 < P e z A := by
  obtain ⟨⟨g,hg⟩, _⟩ :=
    p4Q2ND_originalPosteriorContrast_has_both_signs
      H b hb bpos z.2 e
  have hk : 0 < k e z (g,A) := by
    change 0 <
      K A (Function.update z.2 e g) *
        (s (z.1,Function.update z.2 e g))⁻¹ * D z.2 e g
    exact mul_pos
      (mul_pos
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
          H 2 b A (Function.update z.2 e g))
        (inv_pos.mpr
          (continuousJointSqrtDensity_pos H 2 (by norm_num) b hb
            (z.1,Function.update z.2 e g))))
      hg
  have hCont : Continuous (fun h : Gauge => max (k e z (h,A)) 0) :=
    (p4Q2NF_originalFiberContinuous H b hb e z A).max continuous_const
  have hNe : max (k e z (g,A)) 0 ≠ 0 := by
    rw [max_eq_left hk.le]
    exact hk.ne'
  change 0 < ∫ h : Gauge, max (k e z (h,A)) 0 ∂mu
  exact integral_pos_of_integrable_nonneg_nonzero hCont
    (p4Q2NF_originalFiberPositiveLobe_integrable H b hb e z A)
    (fun h => le_max_right _ _) hNe

/-- The negative side of the SAME genuine JH signed fiber also has
STRICTLY POSITIVE Haar mass, despite all source link values frozen. -/
theorem p4Q2NF_originalPhysicalWeightedNegativeLobeMass_pos
    (bpos : 0 < b) (e : Link) (z : Cfg × Cfg) (A : Cfg) :
    0 < N e z A := by
  obtain ⟨_, ⟨g,hg⟩⟩ :=
    p4Q2ND_originalPosteriorContrast_has_both_signs
      H b hb bpos z.2 e
  have hk : k e z (g,A) < 0 := by
    change
      K A (Function.update z.2 e g) *
        (s (z.1,Function.update z.2 e g))⁻¹ * D z.2 e g < 0
    exact mul_neg_of_pos_of_neg
      (mul_pos
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
          H 2 b A (Function.update z.2 e g))
        (inv_pos.mpr
          (continuousJointSqrtDensity_pos H 2 (by norm_num) b hb
            (z.1,Function.update z.2 e g))))
      hg
  have hkNeg : 0 < -(k e z (g,A)) := neg_pos.mpr hk
  have hCont : Continuous (fun h : Gauge => max (-(k e z (h,A))) 0) :=
    ((p4Q2NF_originalFiberContinuous H b hb e z A).neg).max
      continuous_const
  have hNe : max (-(k e z (g,A))) 0 ≠ 0 := by
    rw [max_eq_left hkNeg.le]
    exact hkNeg.ne'
  change 0 < ∫ h : Gauge, max (-(k e z (h,A))) 0 ∂mu
  exact integral_pos_of_integrable_nonneg_nonzero hCont
    (p4Q2NF_originalFiberNegativeLobe_integrable H b hb e z A)
    (fun h => le_max_right _ _) hNe

/-- The TWO original physical Wilson–Perron weighted signed lobes
are simultaneously nonzero for ALL b>0, H,e,z,A. -/
theorem p4Q2NF_originalPhysicalWeightedBothLobes_pos
    (bpos : 0 < b) (e : Link) (z : Cfg × Cfg) (A : Cfg) :
    0 < P e z A ∧ 0 < N e z A := by
  exact ⟨p4Q2NF_originalPhysicalWeightedPositiveLobeMass_pos
    H b hb bpos e z A,
    p4Q2NF_originalPhysicalWeightedNegativeLobeMass_pos
      H b hb bpos e z A⟩

/-- Exact signed physical JH representer as the DIFFERENCE of
the TWO strictly positive original Wilson–Perron weighted lobe masses. -/
theorem p4Q2NF_originalPhysicalRepresenter_eq_weightedLobeDifference
    (e : Link) (z : Cfg × Cfg) (A : Cfg) :
    r e z A = P e z A - N e z A := by
  let F : Gauge → ℝ := fun g => k e z (g,A)
  have hpInt :
      Integrable (fun g : Gauge => max (F g) 0) mu :=
    p4Q2NF_originalFiberPositiveLobe_integrable H b hb e z A
  have hnInt :
      Integrable (fun g : Gauge => max (-(F g)) 0) mu :=
    p4Q2NF_originalFiberNegativeLobe_integrable H b hb e z A
  rw [p4Q2JH_originalFiberRepresenter_apply H b hb e z A]
  change (∫ g : Gauge, F g ∂mu) =
      (∫ g : Gauge, max (F g) 0 ∂mu) -
        (∫ g : Gauge, max (-(F g)) 0 ∂mu)
  calc
    (∫ g : Gauge, F g ∂mu) =
        ∫ g : Gauge, (max (F g) 0 - max (-(F g)) 0) ∂mu := by
          apply integral_congr_ae
          filter_upwards with g
          exact (p4Q2NF_real_signed_parts (F g)).1.symm
    _ = (∫ g : Gauge, max (F g) 0 ∂mu) -
        (∫ g : Gauge, max (-(F g)) 0 ∂mu) :=
      integral_sub hpInt hnInt

/-- The absolute integral strength of the ORIGINAL weighted physical
signed fiber equals the SUM of its positive and negative masses.
In contrast, its signed Riesz representer is the DIFFERENCE. -/
theorem p4Q2NF_originalPhysicalWeightedFiber_absIntegral_eq_lobeSum
    (e : Link) (z : Cfg × Cfg) (A : Cfg) :
    (∫ g : Gauge, |k e z (g,A)| ∂mu) =
      P e z A + N e z A := by
  let F : Gauge → ℝ := fun g => k e z (g,A)
  have hpInt :
      Integrable (fun g : Gauge => max (F g) 0) mu :=
    p4Q2NF_originalFiberPositiveLobe_integrable H b hb e z A
  have hnInt :
      Integrable (fun g : Gauge => max (-(F g)) 0) mu :=
    p4Q2NF_originalFiberNegativeLobe_integrable H b hb e z A
  change (∫ g : Gauge, |F g| ∂mu) =
      (∫ g : Gauge, max (F g) 0 ∂mu) +
        (∫ g : Gauge, max (-(F g)) 0 ∂mu)
  calc
    (∫ g : Gauge, |F g| ∂mu) =
        ∫ g : Gauge, (max (F g) 0 + max (-(F g)) 0) ∂mu := by
          apply integral_congr_ae
          filter_upwards with g
          exact (p4Q2NF_real_signed_parts (F g)).2.symm
    _ = (∫ g : Gauge, max (F g) 0 ∂mu) +
        (∫ g : Gauge, max (-(F g)) 0 ∂mu) :=
      integral_add hpInt hnInt

/-- The true positive-beta physical JH signed representer exhibits
STRICT Haar cancellation, never full absolute-mass alignment.
It MAY still cancel COMPLETELY. -/
theorem p4Q2NF_originalPhysicalRepresenter_strictCancellation
    (bpos : 0 < b) (e : Link) (z : Cfg × Cfg) (A : Cfg) :
    |r e z A| < ∫ g : Gauge, |k e z (g,A)| ∂mu := by
  obtain ⟨hP, hN⟩ :=
    p4Q2NF_originalPhysicalWeightedBothLobes_pos H b hb bpos e z A
  rw [p4Q2NF_originalPhysicalRepresenter_eq_weightedLobeDifference
    H b hb e z A,
    p4Q2NF_originalPhysicalWeightedFiber_absIntegral_eq_lobeSum
      H b hb e z A]
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- MQ's EXACT original complete SU(2) Wilson one-slab kernel
times the TRUE local integrated signed two-posterior score equals
the two positive original Wilson–Perron weighted lobe masses'
difference. -/
theorem p4Q2NF_originalSignedScore_kernelMul_eq_weightedLobeDifference
    (e : Link) (z : Cfg × Cfg) (A : Cfg) :
    K A z.2 * PsiC e z A = P e z A - N e z A := by
  calc
    K A z.2 * PsiC e z A =
        r e z A :=
      (p4Q2MQ_originalSignedRiesz_eq_globalKernel_mul_localProfile
        H b hb e z A).symm
    _ = P e z A - N e z A :=
      p4Q2NF_originalPhysicalRepresenter_eq_weightedLobeDifference
        H b hb e z A

/-- EXACT AND COMPLETE pointwise obstruction: the ORIGINAL
integrated signed posterior score is zero precisely when its genuine
positive and negative full Wilson–Perron weighted lobe masses match.
The Wilson kernel normalization is already proven STRICTLY positive. -/
theorem p4Q2NF_originalSignedScore_zero_iff_weightedLobes_balance
    (e : Link) (z : Cfg × Cfg) (A : Cfg) :
    PsiC e z A = 0 ↔ P e z A = N e z A := by
  have hK :
      K A z.2 ≠ 0 :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
      H 2 b A z.2).ne'
  have hEq :=
    p4Q2NF_originalSignedScore_kernelMul_eq_weightedLobeDifference
      H b hb e z A
  constructor
  · intro hZero
    rw [hZero, mul_zero] at hEq
    exact (sub_eq_zero.mp hEq.symm)
  · intro hBalance
    rw [hBalance, sub_self] at hEq
    exact (mul_eq_zero.mp hEq).resolve_left hK

end OriginalWeightedSignedFiber
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NF_originalPhysicalWeightedPositiveLobeMass_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NF_originalPhysicalWeightedNegativeLobeMass_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NF_originalPhysicalWeightedBothLobes_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NF_originalPhysicalRepresenter_eq_weightedLobeDifference
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NF_originalPhysicalWeightedFiber_absIntegral_eq_lobeSum
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NF_originalPhysicalRepresenter_strictCancellation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NF_originalSignedScore_kernelMul_eq_weightedLobeDifference
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NF_originalSignedScore_zero_iff_weightedLobes_balance
