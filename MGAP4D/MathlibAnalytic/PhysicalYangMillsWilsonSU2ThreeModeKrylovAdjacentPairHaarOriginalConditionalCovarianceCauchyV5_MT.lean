import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalNormalizedKernelPhysicalCovarianceV5_MS
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Tactic

/-!
# P4-Q2-MT — true original SU(2) Wilson positive-kernel weighted Cauchy–Schwarz

The actual finite-H positive one-slab Wilson kernel K_b(A,B), original
spatial Haar integration carrier and two-interacting-Wilson-posterior
signed score from MQ/MS remain completely unchanged.

For ANY two continuous functions f,g of the full original configuration:
  (∫ f(A) g(A) K_b(A,B) dHaar_H(A))²
    ≤ (∫ f(A)² K_b(A,B) dHaar_H(A))
      (∫ g(A)² K_b(A,B) dHaar_H(A)).
This uses pinned mathlib Holder (p=q=2) applied to the exact ORIGINAL
functions f*sqrt(K_b), g*sqrt(K_b), with the true positive Wilson kernel
on its original spatial Haar measure. There is no new independent-Haar
conditional posterior, replaced kernel, mixing hypothesis or detector.

The original MQ signed local posterior profile has a genuine continuous
representation as r/K (original JH Riesz density divided by strictly
positive original Wilson one-slab kernel) and is therefore a legitimate
input to the same weighted Cauchy–Schwarz.

This alone is a finite-H upper bound and does NOT prove any spatial
decay, a uniform coercivity floor, source transport across H,
positive-fine arbitrary Krylov depth, H1-C3 or 4D continuum mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2MT_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2MT_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2MT_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2MT_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2MT_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section Frozen
variable (H : ℕ) (b : ℝ) (hb : 0 ≤ b)

local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "haar" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "K" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 b
local notation "Psi" => p4Q2MQ_originalSignedLocalFiberProfile H b hb
local notation "r" => p4Q2JH_originalFiberRepresenter H b hb

/-- The EXISTING two-interacting-original-Wilson-posterior signed score
is continuous in its original spatial configuration. The proof uses
the exact MQ identity Psi = r/K with ORIGINAL positive K, not an
auxiliary distribution or a modified signed receiver. -/
theorem p4Q2MT_originalSignedLocalProfile_continuous
    (e : Link) (z : Cfg × Cfg) :
    Continuous (fun A : Cfg => Psi e z A) := by
  have hK : Continuous (fun A : Cfg => K A z.2) :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_right_continuous
      H 2 b z.2
  have hKne : ∀ A : Cfg, K A z.2 ≠ 0 := by
    intro A
    exact (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
      H 2 b A z.2).ne'
  have hR : Continuous (fun A : Cfg => r e z A) :=
    (r e z).continuous
  have hEq : (fun A : Cfg => Psi e z A) =
      (fun A : Cfg => r e z A / K A z.2) := by
    funext A
    exact (p4Q2MQ_originalSignedRiesz_div_originalKernel_eq_localProfile
      H b hb e z A).symm
  rw [hEq]
  exact hR.div hK hKne

/-- The pinned mathlib p=q=2 Hölder inequality gives exact
Cauchy–Schwarz for the ORIGINAL positive one-slab Wilson kernel
weight, with arbitrary true finite-H spatial continuous sources.
There is no assumed spatial mixing, covariance vanishing or
independently sampled Haar posterior. -/
theorem p4Q2MT_originalWilsonKernel_weightedCauchySchwarz
    (z : Cfg × Cfg) (f g : C(Cfg, ℝ)) :
    (∫ A : Cfg, f A * g A * K A z.2 ∂haar)^2 ≤
      (∫ A : Cfg, (f A)^2 * K A z.2 ∂haar) *
      (∫ A : Cfg, (g A)^2 * K A z.2 ∂haar) := by
  let k : Cfg → ℝ := fun A => K A z.2
  let F : Cfg → ℝ := fun A => f A * Real.sqrt (k A)
  let G : Cfg → ℝ := fun A => g A * Real.sqrt (k A)
  have hk_cont : Continuous k :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_right_continuous
      H 2 b z.2
  have hFcont : Continuous F :=
    f.continuous.mul (Real.continuous_sqrt.comp hk_cont)
  have hGcont : Continuous G :=
    g.continuous.mul (Real.continuous_sqrt.comp hk_cont)
  have hFlp : MemLp F (2 : ENNReal) haar :=
    hFcont.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hGlp : MemLp G (2 : ENNReal) haar :=
    hGcont.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hHolder :
      (∫ A : Cfg, |F A| * |G A| ∂haar) ≤
        Real.sqrt (∫ A : Cfg, (F A)^2 ∂haar) *
          Real.sqrt (∫ A : Cfg, (G A)^2 ∂haar) := by
    have h :=
      integral_mul_norm_le_Lp_mul_Lq
        (μ := haar) (p := (2 : ℝ)) (q := (2 : ℝ))
        (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩)
        (by simpa using hFlp)
        (by simpa using hGlp)
    simpa [Real.norm_eq_abs, Real.sqrt_eq_rpow, Real.rpow_two, sq_abs] using h
  have hAbs :
      |∫ A : Cfg, F A * G A ∂haar| ≤
        ∫ A : Cfg, |F A| * |G A| ∂haar := by
    simpa only [Real.norm_eq_abs, abs_mul] using
      (norm_integral_le_integral_norm
        (μ := haar) (f := fun A : Cfg => F A * G A))
  have hA : 0 ≤ ∫ A : Cfg, (F A)^2 ∂haar :=
    integral_nonneg (fun A => sq_nonneg _)
  have hB : 0 ≤ ∫ A : Cfg, (G A)^2 ∂haar :=
    integral_nonneg (fun A => sq_nonneg _)
  have hRpos :
      0 ≤ Real.sqrt (∫ A : Cfg, (F A)^2 ∂haar) *
        Real.sqrt (∫ A : Cfg, (G A)^2 ∂haar) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hBound := hAbs.trans hHolder
  have hProdNonneg :
      0 ≤
        (Real.sqrt (∫ A : Cfg, (F A)^2 ∂haar) *
          Real.sqrt (∫ A : Cfg, (G A)^2 ∂haar) -
            |∫ A : Cfg, F A * G A ∂haar|) *
        (Real.sqrt (∫ A : Cfg, (F A)^2 ∂haar) *
          Real.sqrt (∫ A : Cfg, (G A)^2 ∂haar) +
            |∫ A : Cfg, F A * G A ∂haar|) :=
    mul_nonneg (sub_nonneg.mpr hBound)
      (add_nonneg hRpos (abs_nonneg _))
  have hRootSq :
      (Real.sqrt (∫ A : Cfg, (F A)^2 ∂haar) *
          Real.sqrt (∫ A : Cfg, (G A)^2 ∂haar))^2 =
        (∫ A : Cfg, (F A)^2 ∂haar) *
        (∫ A : Cfg, (G A)^2 ∂haar) := by
    rw [mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hB]
  have hSq :
      (∫ A : Cfg, F A * G A ∂haar)^2 ≤
        (∫ A : Cfg, (F A)^2 ∂haar) *
        (∫ A : Cfg, (G A)^2 ∂haar) := by
    nlinarith [hProdNonneg, hRootSq, sq_abs (∫ A : Cfg, F A * G A ∂haar)]
  have hCross :
      (∫ A : Cfg, F A * G A ∂haar) =
        ∫ A : Cfg, f A * g A * k A ∂haar := by
    apply integral_congr_ae
    filter_upwards with A
    change (f A * Real.sqrt (k A)) *
        (g A * Real.sqrt (k A)) = f A * g A * k A
    rw [show (f A * Real.sqrt (k A)) *
        (g A * Real.sqrt (k A)) =
          f A * g A * (Real.sqrt (k A))^2 by ring,
      Real.sq_sqrt
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
          H 2 b A z.2).le]
  have hF2 :
      (∫ A : Cfg, (F A)^2 ∂haar) =
        ∫ A : Cfg, (f A)^2 * k A ∂haar := by
    apply integral_congr_ae
    filter_upwards with A
    change (f A * Real.sqrt (k A))^2 = (f A)^2 * k A
    rw [mul_pow, Real.sq_sqrt
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
        H 2 b A z.2).le]
  have hG2 :
      (∫ A : Cfg, (G A)^2 ∂haar) =
        ∫ A : Cfg, (g A)^2 * k A ∂haar := by
    apply integral_congr_ae
    filter_upwards with A
    change (g A * Real.sqrt (k A))^2 = (g A)^2 * k A
    rw [mul_pow, Real.sq_sqrt
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
        H 2 b A z.2).le]
  simpa only [k] using (hCross.symm ▸ (hF2.symm ▸ (hG2.symm ▸ hSq)))

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MT_originalSignedLocalProfile_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MT_originalWilsonKernel_weightedCauchySchwarz
