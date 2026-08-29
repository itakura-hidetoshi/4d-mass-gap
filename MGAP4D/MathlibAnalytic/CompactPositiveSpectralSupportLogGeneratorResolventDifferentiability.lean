import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorResolventIdentity
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End Filter
open scoped InnerProductSpace LinearPMap Topology

noncomputable section

universe u

/-- Canonical ambient resolvent family inside the coercive gap. Outside the gap we
set the value to zero; all analytic statements below are local to `|λ| < c`.
The forward partially defined operator itself is never promoted to a bounded map. -/
noncomputable def realLinearPMapAmbientResolventFamily_of_norm_lower_bound
    {E : Type u}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun)
    (lambda : ℝ) : E →L[ℝ] E :=
  if hlambda : |lambda| < c then
    Classical.choose
      (realLinearPMap_exists_ambientResolvent_norm_le_of_abs_lt_norm_lower_bound
        A c hc hNorm hKer hSurj lambda hlambda).2
  else 0

/-- The canonical ambient resolvent is a left inverse of the actual-domain shift. -/
theorem realLinearPMapAmbientResolventFamily_apply_domainShift
    {E : Type u}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun)
    (lambda : ℝ)
    (hlambda : |lambda| < c)
    (x : A.domain) :
    realLinearPMapAmbientResolventFamily_of_norm_lower_bound
        A c hc hNorm hKer hSurj lambda
      (realLinearPMapDomainShift A lambda x) = (x : E) := by
  rw [realLinearPMapAmbientResolventFamily_of_norm_lower_bound, dif_pos hlambda]
  exact
    (Classical.choose_spec
      (realLinearPMap_exists_ambientResolvent_norm_le_of_abs_lt_norm_lower_bound
        A c hc hNorm hKer hSurj lambda hlambda).2).1 x

/-- Every ambient vector has an actual-domain preimage recorded by the canonical
resolvent. -/
theorem realLinearPMapAmbientResolventFamily_exists_domain_preimage
    {E : Type u}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun)
    (lambda : ℝ)
    (hlambda : |lambda| < c)
    (y : E) :
    ∃ x : A.domain,
      realLinearPMapDomainShift A lambda x = y ∧
      realLinearPMapAmbientResolventFamily_of_norm_lower_bound
        A c hc hNorm hKer hSurj lambda y = (x : E) := by
  rw [realLinearPMapAmbientResolventFamily_of_norm_lower_bound, dif_pos hlambda]
  exact
    (Classical.choose_spec
      (realLinearPMap_exists_ambientResolvent_norm_le_of_abs_lt_norm_lower_bound
        A c hc hNorm hKer hSurj lambda hlambda).2).2.1 y

/-- Sharp one-point norm estimate for the canonical family. -/
theorem realLinearPMapAmbientResolventFamily_norm_le
    {E : Type u}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun)
    (lambda : ℝ)
    (hlambda : |lambda| < c) :
    ‖realLinearPMapAmbientResolventFamily_of_norm_lower_bound
        A c hc hNorm hKer hSurj lambda‖ ≤ (c - |lambda|)⁻¹ := by
  rw [realLinearPMapAmbientResolventFamily_of_norm_lower_bound, dif_pos hlambda]
  exact
    (Classical.choose_spec
      (realLinearPMap_exists_ambientResolvent_norm_le_of_abs_lt_norm_lower_bound
        A c hc hNorm hKer hSurj lambda hlambda).2).2.2

/-- The canonical ambient family satisfies the exact resolvent identity throughout
the coercive gap. -/
theorem realLinearPMapAmbientResolventFamily_sub_eq_smul_comp
    {E : Type u}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun)
    (lambda mu : ℝ)
    (hlambda : |lambda| < c)
    (hmu : |mu| < c) :
    let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
      A c hc hNorm hKer hSurj
    F lambda - F mu = (lambda - mu) • (F lambda).comp (F mu) := by
  dsimp only
  exact realLinearPMap_ambientResolvent_sub_eq_smul_comp
    A lambda mu
    (realLinearPMapAmbientResolventFamily_of_norm_lower_bound
      A c hc hNorm hKer hSurj lambda)
    (realLinearPMapAmbientResolventFamily_of_norm_lower_bound
      A c hc hNorm hKer hSurj mu)
    (realLinearPMapAmbientResolventFamily_apply_domainShift
      A c hc hNorm hKer hSurj lambda hlambda)
    (realLinearPMapAmbientResolventFamily_exists_domain_preimage
      A c hc hNorm hKer hSurj mu hmu)

/-- Uniform local Lipschitz estimate on every closed symmetric interval strictly
inside the coercive gap. -/
theorem realLinearPMapAmbientResolventFamily_sub_norm_le_inner_gap
    {E : Type u}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (A : E →ₗ.[ℝ] E)
    (c d : ℝ)
    (hc : 0 < c)
    (hd : 0 ≤ d)
    (hdc : d < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun)
    (lambda mu : ℝ)
    (hlambda : |lambda| ≤ d)
    (hmu : |mu| ≤ d) :
    let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
      A c hc hNorm hKer hSurj
    ‖F lambda - F mu‖ ≤ |lambda - mu| * (c - d)⁻¹ ^ 2 := by
  dsimp only
  have hlambda' : |lambda| < c := lt_of_le_of_lt hlambda hdc
  have hmu' : |mu| < c := lt_of_le_of_lt hmu hdc
  have hcd : 0 < c - d := sub_pos.mpr hdc
  have hclambda : c - d ≤ c - |lambda| := sub_le_sub_left hlambda c
  have hcmu : c - d ≤ c - |mu| := sub_le_sub_left hmu c
  have hinvlambda : (c - |lambda|)⁻¹ ≤ (c - d)⁻¹ := inv_anti₀ hcd hclambda
  have hinvmu : (c - |mu|)⁻¹ ≤ (c - d)⁻¹ := inv_anti₀ hcd hcmu
  have htwo := realLinearPMap_ambientResolvent_sub_norm_le
    A c lambda mu
    (realLinearPMapAmbientResolventFamily_of_norm_lower_bound
      A c hc hNorm hKer hSurj lambda)
    (realLinearPMapAmbientResolventFamily_of_norm_lower_bound
      A c hc hNorm hKer hSurj mu)
    (realLinearPMapAmbientResolventFamily_apply_domainShift
      A c hc hNorm hKer hSurj lambda hlambda')
    (realLinearPMapAmbientResolventFamily_exists_domain_preimage
      A c hc hNorm hKer hSurj mu hmu')
    (realLinearPMapAmbientResolventFamily_norm_le
      A c hc hNorm hKer hSurj lambda hlambda')
    (realLinearPMapAmbientResolventFamily_norm_le
      A c hc hNorm hKer hSurj mu hmu')
    hlambda' hmu'
  calc
    ‖realLinearPMapAmbientResolventFamily_of_norm_lower_bound
        A c hc hNorm hKer hSurj lambda -
      realLinearPMapAmbientResolventFamily_of_norm_lower_bound
        A c hc hNorm hKer hSurj mu‖
        ≤ |lambda - mu| * (c - |lambda|)⁻¹ * (c - |mu|)⁻¹ := htwo
    _ ≤ |lambda - mu| * (c - d)⁻¹ * (c - d)⁻¹ := by
      have h1 :
          |lambda - mu| * (c - |lambda|)⁻¹ ≤
            |lambda - mu| * (c - d)⁻¹ :=
        mul_le_mul_of_nonneg_left hinvlambda (abs_nonneg _)
      have h2 :
          |lambda - mu| * (c - |lambda|)⁻¹ * (c - |mu|)⁻¹ ≤
            (|lambda - mu| * (c - d)⁻¹) * (c - |mu|)⁻¹ :=
        mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr (sub_nonneg.mpr (le_of_lt hmu')))
      exact h2.trans
        (mul_le_mul_of_nonneg_left hinvmu
          (mul_nonneg (abs_nonneg _) (inv_nonneg.mpr hcd.le)))
    _ = |lambda - mu| * (c - d)⁻¹ ^ 2 := by ring

/-- Exact first-order remainder identity.  This is the algebraic core of
operator-norm differentiability: after subtracting the candidate derivative
`F(λ) ∘ F(λ)`, one gains a second resolvent difference. -/
theorem realLinearPMapAmbientResolventFamily_firstOrderRemainder_eq
    {E : Type u}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun)
    (lambda mu : ℝ)
    (hlambda : |lambda| < c)
    (hmu : |mu| < c) :
    let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
      A c hc hNorm hKer hSurj
    F mu - F lambda -
        (mu - lambda) • (F lambda).comp (F lambda) =
      (mu - lambda) • ((F mu - F lambda).comp (F lambda)) := by
  dsimp only
  let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
    A c hc hNorm hKer hSurj
  have hid : F mu - F lambda = (mu - lambda) • (F mu).comp (F lambda) :=
    realLinearPMapAmbientResolventFamily_sub_eq_smul_comp
      A c hc hNorm hKer hSurj mu lambda hmu hlambda
  calc
    F mu - F lambda - (mu - lambda) • (F lambda).comp (F lambda) =
        (mu - lambda) • (F mu).comp (F lambda) -
          (mu - lambda) • (F lambda).comp (F lambda) := by rw [hid]
    _ = (mu - lambda) •
        ((F mu).comp (F lambda) - (F lambda).comp (F lambda)) := by
      module
    _ = (mu - lambda) • ((F mu - F lambda).comp (F lambda)) := by
      congr 1
      ext y
      simp

/-- Quadratic Taylor remainder on every strictly smaller symmetric interval.
This gives the quantitative `O(|μ-λ|²)` estimate behind the derivative
`F'(λ)=F(λ)²`. -/
theorem realLinearPMapAmbientResolventFamily_firstOrderRemainder_norm_le_inner_gap
    {E : Type u}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (A : E →ₗ.[ℝ] E)
    (c d : ℝ)
    (hc : 0 < c)
    (hd : 0 ≤ d)
    (hdc : d < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun)
    (lambda mu : ℝ)
    (hlambda : |lambda| ≤ d)
    (hmu : |mu| ≤ d) :
    let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
      A c hc hNorm hKer hSurj
    ‖F mu - F lambda - (mu - lambda) • (F lambda).comp (F lambda)‖ ≤
      |mu - lambda| ^ 2 * (c - d)⁻¹ ^ 3 := by
  dsimp only
  have hlambda' : |lambda| < c := lt_of_le_of_lt hlambda hdc
  have hmu' : |mu| < c := lt_of_le_of_lt hmu hdc
  rw [realLinearPMapAmbientResolventFamily_firstOrderRemainder_eq
    A c hc hNorm hKer hSurj lambda mu hlambda' hmu']
  rw [norm_smul, Real.norm_eq_abs]
  have hdiff := realLinearPMapAmbientResolventFamily_sub_norm_le_inner_gap
    A c d hc hd hdc hNorm hKer hSurj mu lambda hmu hlambda
  have hFlambda0 := realLinearPMapAmbientResolventFamily_norm_le
    A c hc hNorm hKer hSurj lambda hlambda'
  have hcd : 0 < c - d := sub_pos.mpr hdc
  have hclambda : c - d ≤ c - |lambda| := sub_le_sub_left hlambda c
  have hinvlambda : (c - |lambda|)⁻¹ ≤ (c - d)⁻¹ := inv_anti₀ hcd hclambda
  have hFlambda :
      ‖realLinearPMapAmbientResolventFamily_of_norm_lower_bound
        A c hc hNorm hKer hSurj lambda‖ ≤ (c - d)⁻¹ :=
    hFlambda0.trans hinvlambda
  have hcomp :
      ‖(realLinearPMapAmbientResolventFamily_of_norm_lower_bound
          A c hc hNorm hKer hSurj mu -
        realLinearPMapAmbientResolventFamily_of_norm_lower_bound
          A c hc hNorm hKer hSurj lambda).comp
        (realLinearPMapAmbientResolventFamily_of_norm_lower_bound
          A c hc hNorm hKer hSurj lambda)‖ ≤
      ‖realLinearPMapAmbientResolventFamily_of_norm_lower_bound
          A c hc hNorm hKer hSurj mu -
        realLinearPMapAmbientResolventFamily_of_norm_lower_bound
          A c hc hNorm hKer hSurj lambda‖ *
      ‖realLinearPMapAmbientResolventFamily_of_norm_lower_bound
          A c hc hNorm hKer hSurj lambda‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  calc
    |mu - lambda| *
        ‖(realLinearPMapAmbientResolventFamily_of_norm_lower_bound
            A c hc hNorm hKer hSurj mu -
          realLinearPMapAmbientResolventFamily_of_norm_lower_bound
            A c hc hNorm hKer hSurj lambda).comp
          (realLinearPMapAmbientResolventFamily_of_norm_lower_bound
            A c hc hNorm hKer hSurj lambda)‖
      ≤ |mu - lambda| *
          (‖realLinearPMapAmbientResolventFamily_of_norm_lower_bound
              A c hc hNorm hKer hSurj mu -
            realLinearPMapAmbientResolventFamily_of_norm_lower_bound
              A c hc hNorm hKer hSurj lambda‖ *
            ‖realLinearPMapAmbientResolventFamily_of_norm_lower_bound
              A c hc hNorm hKer hSurj lambda‖) :=
        mul_le_mul_of_nonneg_left hcomp (abs_nonneg _)
    _ ≤ |mu - lambda| *
          ((|mu - lambda| * (c - d)⁻¹ ^ 2) * (c - d)⁻¹) := by
      have hp :
          ‖realLinearPMapAmbientResolventFamily_of_norm_lower_bound
              A c hc hNorm hKer hSurj mu -
            realLinearPMapAmbientResolventFamily_of_norm_lower_bound
              A c hc hNorm hKer hSurj lambda‖ *
            ‖realLinearPMapAmbientResolventFamily_of_norm_lower_bound
              A c hc hNorm hKer hSurj lambda‖ ≤
          (|mu - lambda| * (c - d)⁻¹ ^ 2) * (c - d)⁻¹ := by
        exact mul_le_mul hdiff hFlambda (norm_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_left hp (abs_nonneg _)
    _ = |mu - lambda| ^ 2 * (c - d)⁻¹ ^ 3 := by ring

end

end MathlibAnalytic
end MGAP4D
