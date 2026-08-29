import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorResolventNormBound
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End
open scoped InnerProductSpace LinearPMap

noncomputable section

universe u

/-- Two ambient realizations of actual-domain resolvents satisfy the ordinary
resolvent identity.  The proof only uses the two inverse identities on the
actual domain; the forward operator itself is never promoted to a bounded map. -/
theorem realLinearPMap_ambientResolvent_sub_eq_smul_comp
    {E : Type u}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (A : E →ₗ.[ℝ] E)
    (lambda mu : ℝ)
    (Blambda Bmu : E →L[ℝ] E)
    (hBlambdaLeft : ∀ x : A.domain,
      Blambda (realLinearPMapDomainShift A lambda x) = (x : E))
    (hBmuRight : ∀ y : E, ∃ x : A.domain,
      realLinearPMapDomainShift A mu x = y ∧ Bmu y = (x : E)) :
    Blambda - Bmu = (lambda - mu) • Blambda.comp Bmu := by
  ext y
  rcases hBmuRight y with ⟨x, hx, hBmu⟩
  have hshift :
      realLinearPMapDomainShift A lambda x =
        realLinearPMapDomainShift A mu x + (mu - lambda) • (x : E) := by
    simp [realLinearPMapDomainShift, sub_smul]
    abel
  have hleft := hBlambdaLeft x
  rw [hshift, map_add, map_smul, hx, ← hBmu] at hleft
  change Blambda y - Bmu y = (lambda - mu) • Blambda (Bmu y)
  rw [sub_eq_iff_eq_add]
  calc
    Blambda y = Bmu y - (mu - lambda) • Blambda (Bmu y) := by
      linarith
    _ = Bmu y + (lambda - mu) • Blambda (Bmu y) := by
      congr 1
      rw [← neg_smul, neg_sub]

/-- Quantitative two-point resolvent estimate. -/
theorem realLinearPMap_ambientResolvent_sub_norm_le
    {E : Type u}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (lambda mu : ℝ)
    (Blambda Bmu : E →L[ℝ] E)
    (hBlambdaLeft : ∀ x : A.domain,
      Blambda (realLinearPMapDomainShift A lambda x) = (x : E))
    (hBmuRight : ∀ y : E, ∃ x : A.domain,
      realLinearPMapDomainShift A mu x = y ∧ Bmu y = (x : E))
    (hBlambdaNorm : ‖Blambda‖ ≤ (c - |lambda|)⁻¹)
    (hBmuNorm : ‖Bmu‖ ≤ (c - |mu|)⁻¹)
    (hlambda : |lambda| < c)
    (hmu : |mu| < c) :
    ‖Blambda - Bmu‖ ≤
      |lambda - mu| * (c - |lambda|)⁻¹ * (c - |mu|)⁻¹ := by
  rw [realLinearPMap_ambientResolvent_sub_eq_smul_comp
    A lambda mu Blambda Bmu hBlambdaLeft hBmuRight]
  calc
    ‖(lambda - mu) • Blambda.comp Bmu‖ =
        |lambda - mu| * ‖Blambda.comp Bmu‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    _ ≤ |lambda - mu| * (‖Blambda‖ * ‖Bmu‖) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le Blambda Bmu
    _ ≤ |lambda - mu| *
        ((c - |lambda|)⁻¹ * (c - |mu|)⁻¹) := by
      gcongr
      · exact abs_nonneg _
      · exact norm_nonneg _
      · exact hBlambdaNorm
      · exact hBmuNorm
    _ = |lambda - mu| * (c - |lambda|)⁻¹ * (c - |mu|)⁻¹ := by ring

/-- Coercivity supplies two ambient resolvents simultaneously, together with the
resolvent identity and its quantitative two-point bound. -/
theorem realLinearPMap_exists_ambientResolvent_pair_with_identity_and_norm_bound
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
    ∃ Blambda Bmu : E →L[ℝ] E,
      (∀ x : A.domain,
        Blambda (realLinearPMapDomainShift A lambda x) = (x : E)) ∧
      (∀ y : E, ∃ x : A.domain,
        realLinearPMapDomainShift A lambda x = y ∧ Blambda y = (x : E)) ∧
      (∀ x : A.domain,
        Bmu (realLinearPMapDomainShift A mu x) = (x : E)) ∧
      (∀ y : E, ∃ x : A.domain,
        realLinearPMapDomainShift A mu x = y ∧ Bmu y = (x : E)) ∧
      Blambda - Bmu = (lambda - mu) • Blambda.comp Bmu ∧
      ‖Blambda - Bmu‖ ≤
        |lambda - mu| * (c - |lambda|)⁻¹ * (c - |mu|)⁻¹ := by
  rcases
    (realLinearPMap_exists_ambientResolvent_norm_le_of_abs_lt_norm_lower_bound
      A c hc hNorm hKer hSurj lambda hlambda).2 with
    ⟨Blambda, hBlambdaLeft, hBlambdaRight, hBlambdaNorm⟩
  rcases
    (realLinearPMap_exists_ambientResolvent_norm_le_of_abs_lt_norm_lower_bound
      A c hc hNorm hKer hSurj mu hmu).2 with
    ⟨Bmu, hBmuLeft, hBmuRight, hBmuNorm⟩
  refine ⟨Blambda, Bmu, hBlambdaLeft, hBlambdaRight,
    hBmuLeft, hBmuRight, ?_, ?_⟩
  · exact realLinearPMap_ambientResolvent_sub_eq_smul_comp
      A lambda mu Blambda Bmu hBlambdaLeft hBmuRight
  · exact realLinearPMap_ambientResolvent_sub_norm_le
      A c lambda mu Blambda Bmu hBlambdaLeft hBmuRight
      hBlambdaNorm hBmuNorm hlambda hmu

/-- On every strictly smaller symmetric interval, the ambient resolvent family has
a uniform Lipschitz constant.  This is the quantitative local-continuity statement
needed for the open gap. -/
theorem realLinearPMap_exists_ambientResolvent_pair_lipschitz_on_inner_gap
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
    ∃ Blambda Bmu : E →L[ℝ] E,
      (∀ x : A.domain,
        Blambda (realLinearPMapDomainShift A lambda x) = (x : E)) ∧
      (∀ y : E, ∃ x : A.domain,
        realLinearPMapDomainShift A lambda x = y ∧ Blambda y = (x : E)) ∧
      (∀ x : A.domain,
        Bmu (realLinearPMapDomainShift A mu x) = (x : E)) ∧
      (∀ y : E, ∃ x : A.domain,
        realLinearPMapDomainShift A mu x = y ∧ Bmu y = (x : E)) ∧
      ‖Blambda - Bmu‖ ≤ |lambda - mu| * (c - d)⁻¹ ^ 2 := by
  have hlambda' : |lambda| < c := lt_of_le_of_lt hlambda hdc
  have hmu' : |mu| < c := lt_of_le_of_lt hmu hdc
  rcases realLinearPMap_exists_ambientResolvent_pair_with_identity_and_norm_bound
      A c hc hNorm hKer hSurj lambda mu hlambda' hmu' with
    ⟨Blambda, Bmu, hBlambdaLeft, hBlambdaRight,
      hBmuLeft, hBmuRight, hid, hdiff⟩
  refine ⟨Blambda, Bmu, hBlambdaLeft, hBlambdaRight,
    hBmuLeft, hBmuRight, ?_⟩
  have hcd : 0 < c - d := sub_pos.mpr hdc
  have hclambda : c - d ≤ c - |lambda| := sub_le_sub_left hlambda c
  have hcmu : c - d ≤ c - |mu| := sub_le_sub_left hmu c
  have hinvlambda : (c - |lambda|)⁻¹ ≤ (c - d)⁻¹ := by
    exact inv_anti₀ hcd hclambda
  have hinvmu : (c - |mu|)⁻¹ ≤ (c - d)⁻¹ := by
    exact inv_anti₀ hcd hcmu
  calc
    ‖Blambda - Bmu‖ ≤
        |lambda - mu| * (c - |lambda|)⁻¹ * (c - |mu|)⁻¹ := hdiff
    _ ≤ |lambda - mu| * (c - d)⁻¹ * (c - d)⁻¹ := by
      gcongr
      · exact abs_nonneg _
      · exact inv_nonneg.mpr (sub_nonneg.mpr (le_of_lt hdc))
      · exact hinvlambda
      · exact hinvmu
    _ = |lambda - mu| * (c - d)⁻¹ ^ 2 := by ring

end

end MathlibAnalytic
end MGAP4D
