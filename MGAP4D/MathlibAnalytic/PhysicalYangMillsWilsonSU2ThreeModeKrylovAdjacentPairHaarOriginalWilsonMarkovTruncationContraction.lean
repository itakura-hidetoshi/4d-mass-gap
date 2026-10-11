import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalBoundedCoreKernelExactFrontier
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Tactic

/-!
# P4-Q2-CM: Markov truncation contraction of the genuine original Wilson Haar reference

CL identified the original Wilson Haar Riesz kernel on the entire bounded-core
image with the intrinsic physical constant line. Here we construct the real
symmetric truncation and show its 1-Lipschitz Markov property, followed by
an ACTUAL fiberwise Haar-variance contraction.

Every physical right and left original Wilson one-link Haar reference retains
its original outer physical joint mass and the exp(-32 beta) coefficient.
The resulting contraction is summed over all genuine six right and six left
spatial colors to yield the LITERAL bounded Wilson concrete core contraction.

The full physical joint-L² nonlinear truncation extension, density/closedness
argument, general Riesz kernel equality and spectral gap remain independent
follow-up proof obligations. No physical law is replaced, and no new axioms
are introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section

set_option maxHeartbeats 2600000
set_option synthInstance.maxHeartbeats 850000

attribute [local instance]
  groundStateJointOneLinkCenteredResidualSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkCenteredResidualSpecialUnitaryCompactSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkCenteredResidualSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitaryBorelSpace
  groundStateJointOneLinkCenteredResidualSpatialLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkUnique
  p4Q2BAColorLinksFintype

/-- Symmetric Markov clipping at a nonnegative level M. -/
def p4Q2CM_truncate (M : ℝ) (x : ℝ) : ℝ :=
  max (-M) (min M x)

/-- Symmetric clipping is 1-Lipschitz; no physical measure occurs here. -/
theorem p4Q2CM_truncate_abs_sub_le (M x y : ℝ) :
    |p4Q2CM_truncate M x - p4Q2CM_truncate M y| ≤ |x - y| := by
  have hmin : |min M x - min M y| ≤ |x - y| := by
    simpa only [sub_self, abs_zero, max_eq_right (abs_nonneg (x - y))] using
      (abs_min_sub_min_le_max M x M y)
  calc
    |p4Q2CM_truncate M x - p4Q2CM_truncate M y| =
        |max (min M x) (-M) - max (min M y) (-M)| := by
          simp only [p4Q2CM_truncate, max_comm]
    _ ≤ |min M x - min M y| := abs_max_sub_max_le_abs _ _ _
    _ ≤ |x - y| := hmin

theorem p4Q2CM_truncate_lipschitz (M : ℝ) :
    LipschitzWith 1 (p4Q2CM_truncate M) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa [Real.dist_eq] using
    (p4Q2CM_truncate_abs_sub_le M x y)

theorem p4Q2CM_truncate_continuous (M : ℝ) :
    Continuous (p4Q2CM_truncate M) :=
  (p4Q2CM_truncate_lipschitz M).continuous

theorem p4Q2CM_truncate_zero (M : ℝ) (hM : 0 ≤ M) :
    p4Q2CM_truncate M 0 = 0 := by
  simp [p4Q2CM_truncate, min_eq_right hM, max_eq_right (neg_nonpos.mpr hM)]

theorem p4Q2CM_truncate_mem (M : ℝ) (hM : 0 ≤ M) (x : ℝ) :
    -M ≤ p4Q2CM_truncate M x ∧ p4Q2CM_truncate M x ≤ M := by
  have hlow : -M ≤ M := by linarith
  exact ⟨le_max_left _ _, max_le hlow (min_le_left _ _)⟩

/-- A probability variance contracts under any 1-Lipschitz composition
whenever the original and composed observables actually belong to L².
The proof uses the best constant approximation property of variance:
Var(Y) ≤ E[(Y - phi(E[X]))²] ≤ E[(X - E[X])²]. -/
private theorem p4Q2CM_variance_lipschitz_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (phi : ℝ → ℝ)
    (hX : MemLp X 2 μ)
    (hY : MemLp (fun u => phi (X u)) 2 μ)
    (hphi : ∀ x y : ℝ, |phi x - phi y| ≤ |x - y|) :
    variance (fun u => phi (X u)) μ ≤ variance X μ := by
  let Y : Ω → ℝ := fun u => phi (X u)
  let m : ℝ := ∫ u, X u ∂μ
  let c : ℝ := phi m
  have hXsub : MemLp (fun u : Ω => X u - m) 2 μ := by
    simpa only [Pi.sub_apply] using (hX.sub (memLp_const m))
  have hYsub : MemLp (fun u : Ω => Y u - c) 2 μ := by
    simpa only [Pi.sub_apply] using (hY.sub (memLp_const c))
  have hXsq : Integrable (fun u : Ω => (X u - m) ^ 2) μ := by
    simpa only [Pi.pow_apply] using hXsub.integrable_sq
  have hYsq : Integrable (fun u : Ω => (Y u - c) ^ 2) μ := by
    simpa only [Pi.pow_apply] using hYsub.integrable_sq
  have hpoint : ∀ u : Ω, (Y u - c) ^ 2 ≤ (X u - m) ^ 2 := by
    intro u
    exact (sq_le_sq).2 (hphi (X u) m)
  calc
    variance (fun u => phi (X u)) μ =
        variance (fun u => Y u - c) μ :=
      (variance_sub_const hY.aestronglyMeasurable c).symm
    _ ≤ ∫ u, (Y u - c) ^ 2 ∂μ := by
      simpa only [Pi.pow_apply] using
        (variance_le_expectation_sq hYsub.aestronglyMeasurable)
    _ ≤ ∫ u, (X u - m) ^ 2 ∂μ :=
      integral_mono_ae hYsq hXsq (Filter.Eventually.of_forall hpoint)
    _ = variance X μ := by
      exact (variance_eq_integral hX.aemeasurable).symm

/-- The EXACT ENNReal evariance used by the original Wilson link reference
contracts under a 1-Lipschitz composition on the genuine Haar L² fiber. -/
theorem p4Q2CM_evariance_lipschitz_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (phi : ℝ → ℝ)
    (hX : MemLp X 2 μ)
    (hY : MemLp (fun u => phi (X u)) 2 μ)
    (hphi : ∀ x y : ℝ, |phi x - phi y| ≤ |x - y|) :
    evariance (fun u => phi (X u)) μ ≤ evariance X μ := by
  calc
    evariance (fun u => phi (X u)) μ =
        ENNReal.ofReal (variance (fun u => phi (X u)) μ) :=
      hY.ofReal_variance_eq.symm
    _ ≤ ENNReal.ofReal (variance X μ) :=
      ENNReal.ofReal_le_ofReal
        (p4Q2CM_variance_lipschitz_le μ X phi hX hY hphi)
    _ = evariance X μ := hX.ofReal_variance_eq

/-- Applying the same 1-Lipschitz symmetric truncation pointwise to an
ACTUAL strongly measurable bounded joint observable preserves membership
in the ORIGINAL bounded Wilson physical core. -/
noncomputable def p4Q2CM_truncateCore (H N : ℕ)
    (M : ℝ) (hM : 0 ≤ M)
    (F : p4Q2BP_originalBoundedStronglyMeasurableCore H N) :
    p4Q2BP_originalBoundedStronglyMeasurableCore H N := by
  refine ⟨(fun z => p4Q2CM_truncate M (F.1 z)), ?_⟩
  obtain ⟨hF, _⟩ := F.property
  refine ⟨((p4Q2CM_truncate_continuous M).measurable.comp
    hF.measurable).stronglyMeasurable, ⟨M, ?_⟩⟩
  intro z
  rw [Real.norm_eq_abs]
  exact abs_le.mpr (p4Q2CM_truncate_mem M hM (F.1 z))

section OriginalWilson

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "G" => Matrix.specialUnitaryGroup (Fin N) ℂ
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Core" =>
  p4Q2BP_originalBoundedStronglyMeasurableCore H N
local notation "C12" =>
  PeriodicHypercubicEvenGroundStateTwoSidedSpatialColor
local notation "Section" =>
  periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection H N

/-- Markov contraction for one ACTUAL original right Wilson Haar reference.
The original conditional mass of its physical fiber and exp(-32 beta) factor
remain exactly the same; only the target-group observable is clipped. -/
theorem p4Q2CM_originalRightLinkHaar_truncate_le
    (M : ℝ) (hM : 0 ≤ M) (target : Link)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    p4Q2AZ_originalJointHaarReferenceEnergy H N hN beta hbeta target
        (fun z => p4Q2CM_truncate M (F z)) ≤
      p4Q2AZ_originalJointHaarReferenceEnergy
        H N hN beta hbeta target F := by
  let μLink : Measure G := normalizedCompactHaar G
  letI : IsProbabilityMeasure μLink := by
    dsimp [μLink]
    infer_instance
  let μOuter :=
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
      (Measure.pi (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target => μLink))
  let mass := periodicHypercubicEvenSpecialUnitaryOriginalGroundStateOneLinkOuterMass
      H N hN beta hbeta target
  let k : ENNReal := ENNReal.ofReal (Real.exp (-32 * beta))
  change (∫⁻ ctx,
    mass ctx * (k *
      evariance (fun u : G => p4Q2CM_truncate M (Section target F ctx.1 ctx.2 u))
        μLink) ∂μOuter) ≤
      (∫⁻ ctx,
        mass ctx * (k * evariance (Section target F ctx.1 ctx.2) μLink) ∂μOuter)
  apply lintegral_mono
  intro ctx
  let X : G → ℝ := Section target F ctx.1 ctx.2
  have hX : MemLp X 2 μLink :=
    p4Q2BJ_originalJointOneLinkSection_memLp
      H N target F hF bound hbound ctx.1 ctx.2
  have hY : MemLp (fun u : G => p4Q2CM_truncate M (X u)) 2 μLink := by
    simpa only [Function.comp_def] using
      (p4Q2CM_truncate_lipschitz M).comp_memLp
        (p4Q2CM_truncate_zero M hM) hX
  have hvar :
      evariance (fun u : G => p4Q2CM_truncate M (X u)) μLink ≤
        evariance X μLink :=
    p4Q2CM_evariance_lipschitz_le μLink X (p4Q2CM_truncate M)
      hX hY (p4Q2CM_truncate_abs_sub_le M)
  have hw := mul_le_mul_left (mul_le_mul_left hvar k) (mass ctx)
  simpa only [X, mul_comm, mul_left_comm, mul_assoc] using hw

/-- Every ACTUAL left Wilson Haar reference, obtained by the previously
proved physical endpoint-swap, has the same Markov contraction. -/
theorem p4Q2CM_originalLeftLinkHaar_truncate_le
    (M : ℝ) (hM : 0 ≤ M) (target : Link)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    p4Q2BB_originalLeftLinkHaarReferenceEnergy H N hN beta hbeta target
        (fun z => p4Q2CM_truncate M (F z)) ≤
      p4Q2BB_originalLeftLinkHaarReferenceEnergy
        H N hN beta hbeta target F := by
  change
    p4Q2AZ_originalJointHaarReferenceEnergy H N hN beta hbeta target
        (fun z : Joint => p4Q2CM_truncate M (p4Q2BB_swapConcrete H N F z)) ≤
      p4Q2AZ_originalJointHaarReferenceEnergy H N hN beta hbeta target
        (p4Q2BB_swapConcrete H N F)
  exact p4Q2CM_originalRightLinkHaar_truncate_le H N hN beta hbeta
    M hM target
    (p4Q2BB_swapConcrete H N F)
    (p4Q2BB_swapConcrete_stronglyMeasurable H N F hF)
    bound (p4Q2BB_swapConcrete_norm_le H N F bound hbound)

/-- Actual original right- and left-color normalized Haar reference
averages separately contract, preserving ALL physical links in the colors. -/
theorem p4Q2CM_originalTwelveColorHaar_truncate_le
    (M : ℝ) (hM : 0 ≤ M) (c : C12)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    p4Q2BB_twelveColorOriginalHaarReferenceAverage H N hN beta hbeta c
        (fun z => p4Q2CM_truncate M (F z)) ≤
      p4Q2BB_twelveColorOriginalHaarReferenceAverage
        H N hN beta hbeta c F := by
  classical
  cases c with
  | inl c =>
      change (Fintype.card (p4Q2BA_ColorLinks H c) : ENNReal)⁻¹ *
          (∑ e : p4Q2BA_ColorLinks H c,
            p4Q2AZ_originalJointHaarReferenceEnergy H N hN beta hbeta e.1
              (fun z => p4Q2CM_truncate M (F z))) ≤
        (Fintype.card (p4Q2BA_ColorLinks H c) : ENNReal)⁻¹ *
          (∑ e : p4Q2BA_ColorLinks H c,
            p4Q2AZ_originalJointHaarReferenceEnergy H N hN beta hbeta e.1 F)
      have hsum :
          (∑ e : p4Q2BA_ColorLinks H c,
            p4Q2AZ_originalJointHaarReferenceEnergy H N hN beta hbeta e.1
              (fun z => p4Q2CM_truncate M (F z))) ≤
          (∑ e : p4Q2BA_ColorLinks H c,
            p4Q2AZ_originalJointHaarReferenceEnergy H N hN beta hbeta e.1 F) := by
        apply Finset.sum_le_sum
        intro e _he
        exact p4Q2CM_originalRightLinkHaar_truncate_le
          H N hN beta hbeta M hM e.1 F hF bound hbound
      simpa only [mul_comm] using
        (mul_le_mul_left hsum
          ((Fintype.card (p4Q2BA_ColorLinks H c) : ENNReal)⁻¹))
  | inr c =>
      change (Fintype.card (p4Q2BA_ColorLinks H c) : ENNReal)⁻¹ *
          (∑ e : p4Q2BA_ColorLinks H c,
            p4Q2BB_originalLeftLinkHaarReferenceEnergy H N hN beta hbeta e.1
              (fun z => p4Q2CM_truncate M (F z))) ≤
        (Fintype.card (p4Q2BA_ColorLinks H c) : ENNReal)⁻¹ *
          (∑ e : p4Q2BA_ColorLinks H c,
            p4Q2BB_originalLeftLinkHaarReferenceEnergy H N hN beta hbeta e.1 F)
      have hsum :
          (∑ e : p4Q2BA_ColorLinks H c,
            p4Q2BB_originalLeftLinkHaarReferenceEnergy H N hN beta hbeta e.1
              (fun z => p4Q2CM_truncate M (F z))) ≤
          (∑ e : p4Q2BA_ColorLinks H c,
            p4Q2BB_originalLeftLinkHaarReferenceEnergy H N hN beta hbeta e.1 F) := by
        apply Finset.sum_le_sum
        intro e _he
        exact p4Q2CM_originalLeftLinkHaar_truncate_le
          H N hN beta hbeta M hM e.1 F hF bound hbound
      simpa only [mul_comm] using
        (mul_le_mul_left hsum
          ((Fintype.card (p4Q2BA_ColorLinks H c) : ENNReal)⁻¹))

/-- MAIN CM theorem: the literal ORIGINAL 12-color mass-weighted Wilson Haar
reference is Markovian on its bounded strongly measurable physical core.
No measure substitute or unproved reverse inequality is introduced. -/
theorem p4Q2CM_originalBoundedCoreMarkov_truncate_le
    (M : ℝ) (hM : 0 ≤ M) (F : Core) :
    p4Q2BP_originalCoreReference H N hN beta hbeta
        (p4Q2CM_truncateCore H N M hM F) ≤
      p4Q2BP_originalCoreReference H N hN beta hbeta F := by
  classical
  obtain ⟨hF, ⟨bound, hbound⟩⟩ := F.property
  have hsum :
      (∑ c : C12,
        p4Q2BB_twelveColorOriginalHaarReferenceAverage H N hN beta hbeta c
          (fun z => p4Q2CM_truncate M (F.1 z))) ≤
      (∑ c : C12,
        p4Q2BB_twelveColorOriginalHaarReferenceAverage H N hN beta hbeta c F.1) := by
    apply Finset.sum_le_sum
    intro c _hc
    exact p4Q2CM_originalTwelveColorHaar_truncate_le
      H N hN beta hbeta M hM c F.1 hF bound hbound
  have htop :
      (∑ c : C12,
        p4Q2BB_twelveColorOriginalHaarReferenceAverage
          H N hN beta hbeta c F.1) ≠ ∞ :=
    p4Q2BD_originalWilsonTwelveColorHaarReference_ne_top
      H N hN beta hbeta F.1 hF bound hbound
  have hconcrete :
      (p4Q2CM_truncateCore H N M hM F).1 =
        (fun z => p4Q2CM_truncate M (F.1 z)) := rfl
  simp only [p4Q2BP_originalCoreReference,
    p4Q2BD_originalWilsonTwelveColorHaarReferenceReal, hconcrete]
  exact ENNReal.toReal_mono htop hsum

end OriginalWilson
end

end MathlibAnalytic
end MGAP4D
