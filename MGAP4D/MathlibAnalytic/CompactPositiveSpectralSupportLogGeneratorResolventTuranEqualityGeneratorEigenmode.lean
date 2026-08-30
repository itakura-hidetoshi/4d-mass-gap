import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorResolventTuranEquality
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End Filter
open scoped InnerProductSpace LinearPMap Topology BigOperators

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

universe u

/-- A nonzero eigenmode of the bounded ambient resolvent comes from an actual-domain
eigenmode of the original partially defined operator.  The eigenvalues are related
by the exact reciprocal shift `ρ = λ + r⁻¹`.

The proof uses the canonical actual-domain preimage receipt for the resolvent.
If `Fλ u = r u`, its actual-domain preimage `x` satisfies `(A - λI)x = u` and
`x = r u`.  Thus `r = 0` would force `x = 0` and hence `u = 0`; for nonzero `u`,
rescaling `x` by `r⁻¹` places `u` itself in the true operator domain and yields
the claimed generator eigenvalue. -/
theorem realLinearPMapAmbientResolventFamily_eigenmode_to_domain_eigenmode
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (A : E →ₗ.[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun)
    (lambda : ℝ) (hlambda : |lambda| < c)
    (u : E) (hu : u ≠ 0) (r : ℝ)
    (hr : realLinearPMapAmbientResolventFamily_of_norm_lower_bound
      A c hc hNorm hKer hSurj lambda u = r • u) :
    r ≠ 0 ∧
      ∃ x : A.domain,
        (x : E) = u ∧ A x = (lambda + r⁻¹) • u := by
  let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
    A c hc hNorm hKer hSurj lambda
  rcases realLinearPMapAmbientResolventFamily_exists_domain_preimage
      A c hc hNorm hKer hSurj lambda hlambda u with
    ⟨x, hshift, hFx⟩
  have hxeq : (x : E) = r • u := by
    calc
      (x : E) = F u := by simpa [F] using hFx.symm
      _ = r • u := by simpa [F] using hr
  have hr0 : r ≠ 0 := by
    intro hrzero
    have hxcoe : (x : E) = 0 := by simpa [hrzero] using hxeq
    have hx : x = 0 := by
      apply Subtype.ext
      exact hxcoe
    apply hu
    rw [hx] at hshift
    simpa [realLinearPMapDomainShift] using hshift.symm
  let z : A.domain := r⁻¹ • x
  have hzcoe : (z : E) = u := by
    change r⁻¹ • (x : E) = u
    rw [hxeq]
    simp [smul_smul, hr0]
  have hAx : A x = u + lambda • (x : E) := by
    change A x - lambda • (x : E) = u at hshift
    exact sub_eq_iff_eq_add.mp hshift
  have hcoef : r⁻¹ * (lambda * r) = lambda := by
    calc
      r⁻¹ * (lambda * r) = lambda * (r⁻¹ * r) := by ring
      _ = lambda := by simp [hr0]
  refine ⟨hr0, z, hzcoe, ?_⟩
  calc
    A z = r⁻¹ • A x := by
      change A (r⁻¹ • x) = r⁻¹ • A x
      exact map_smul A r⁻¹ x
    _ = r⁻¹ • (u + lambda • (x : E)) := by rw [hAx]
    _ = r⁻¹ • (u + lambda • (r • u)) := by rw [hxeq]
    _ = (lambda + r⁻¹) • u := by
      simp only [smul_add, smul_smul]
      rw [hcoef, add_smul]
      exact add_comm _ _

/-- Conversely, an actual-domain eigenmode of the original partially defined
operator is an eigenmode of every bounded ambient resolvent in the coercive gap.
The resolvent eigenvalue is exactly `(ρ - λ)⁻¹`; in particular `ρ ≠ λ` follows
from invertibility of the domain shift, rather than being added as an assumption. -/
theorem realLinearPMapAmbientResolventFamily_domain_eigenmode_to_eigenmode
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (A : E →ₗ.[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun)
    (lambda : ℝ) (hlambda : |lambda| < c)
    (u : E) (hu : u ≠ 0) (rho : ℝ) (x : A.domain)
    (hxu : (x : E) = u) (hAx : A x = rho • u) :
    rho ≠ lambda ∧
      realLinearPMapAmbientResolventFamily_of_norm_lower_bound
        A c hc hNorm hKer hSurj lambda u = (rho - lambda)⁻¹ • u := by
  let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
    A c hc hNorm hKer hSurj lambda
  have hshift : realLinearPMapDomainShift A lambda x = (rho - lambda) • u := by
    simp [realLinearPMapDomainShift, hAx, hxu, sub_smul]
  have hdiff0 : rho - lambda ≠ 0 := by
    intro hzero
    have hleft :=
      realLinearPMapAmbientResolventFamily_apply_domainShift
        A c hc hNorm hKer hSurj lambda hlambda x
    have hxzero : (x : E) = 0 := by
      rw [hshift, hzero, zero_smul, map_zero] at hleft
      exact hleft.symm
    apply hu
    rw [← hxu]
    exact hxzero
  have hrholambda : rho ≠ lambda := sub_ne_zero.mp hdiff0
  have hscaled : (rho - lambda) • F u = u := by
    have hleft :=
      realLinearPMapAmbientResolventFamily_apply_domainShift
        A c hc hNorm hKer hSurj lambda hlambda x
    change F (realLinearPMapDomainShift A lambda x) = (x : E) at hleft
    rw [hshift, map_smul, hxu] at hleft
    exact hleft
  refine ⟨hrholambda, ?_⟩
  calc
    F u = (rho - lambda)⁻¹ • ((rho - lambda) • F u) := by
      rw [smul_smul, inv_mul_cancel₀ hdiff0, one_smul]
    _ = (rho - lambda)⁻¹ • u := by rw [hscaled]

/-- Single spectral modes of the bounded ambient resolvent are exactly the
actual-domain spectral modes of the original partially defined operator. -/
theorem realLinearPMapAmbientResolventFamily_eigenmode_iff_domain_eigenmode
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (A : E →ₗ.[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun)
    (lambda : ℝ) (hlambda : |lambda| < c)
    (u : E) (hu : u ≠ 0) :
    let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
      A c hc hNorm hKer hSurj lambda
    (∃ r : ℝ, F u = r • u) ↔
      ∃ rho : ℝ, ∃ x : A.domain, (x : E) = u ∧ A x = rho • u := by
  dsimp only
  constructor
  · rintro ⟨r, hr⟩
    rcases realLinearPMapAmbientResolventFamily_eigenmode_to_domain_eigenmode
      A c hc hNorm hKer hSurj lambda hlambda u hu r hr with
      ⟨_, x, hxu, hAx⟩
    exact ⟨lambda + r⁻¹, x, hxu, hAx⟩
  · rintro ⟨rho, x, hxu, hAx⟩
    rcases realLinearPMapAmbientResolventFamily_domain_eigenmode_to_eigenmode
      A c hc hNorm hKer hSurj lambda hlambda u hu rho x hxu hAx with
      ⟨_, hF⟩
    exact ⟨(rho - lambda)⁻¹, hF⟩

/-- Equality of consecutive factorial-normalized support-resolvent derivative
ratios is therefore equivalent to a single spectral mode of the original
partially defined generator itself, with a genuine domain witness. -/
theorem realLinearPMapAmbientResolventQuadraticAmplitude_derivativeRatio_eq_succ_iff_domain_eigenmode
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : E →ₗ.[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun)
    (hSelf : IsSelfAdjoint A)
    (hQuad : ∀ x : A.domain, c * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E))
    (u : E) (hu : u ≠ 0) (n : ℕ) (lambda : ℝ) (hlambda : |lambda| < c) :
    let q := realLinearPMapAmbientResolventQuadraticAmplitude A c hc hNorm hKer hSurj u
    iteratedDeriv (n + 1) q lambda /
        ((n + 1 : ℝ) * iteratedDeriv n q lambda) =
      iteratedDeriv (n + 2) q lambda /
        ((n + 2 : ℝ) * iteratedDeriv (n + 1) q lambda) ↔
      ∃ rho : ℝ, ∃ x : A.domain, (x : E) = u ∧ A x = rho • u := by
  dsimp only
  have hratio :=
    realLinearPMapAmbientResolventQuadraticAmplitude_derivativeRatio_eq_succ_iff_eigenmode
      A c hc hNorm hKer hSurj hSelf hQuad u hu n lambda hlambda
  have hmode :=
    realLinearPMapAmbientResolventFamily_eigenmode_iff_domain_eigenmode
      A c hc hNorm hKer hSurj lambda hlambda u hu
  exact hratio.trans hmode

end

end MathlibAnalytic
end MGAP4D
