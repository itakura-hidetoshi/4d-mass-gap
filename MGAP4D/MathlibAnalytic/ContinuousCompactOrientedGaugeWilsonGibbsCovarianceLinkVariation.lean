import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonGibbsCovarianceGlobalOscillation
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonDobrushinVariationPropagation
import Mathlib.Tactic

/-!
# Gibbs covariance controlled by the total physical-link variation

The compact oriented configuration space is a finite product over physical
positive links.  Therefore two configurations can be joined by replacing one
link at a time.  A proof-relevant link-variation profile telescopes along this
finite path, giving a global oscillation bound by the sum of all link
variations.  Combined with the canonical Gibbs global-oscillation estimate,
this yields a direct finite-volume covariance bound.

No Dobrushin threshold or support separation is used in this file.  Those enter
later through quantitative bounds on the propagated centered variation profile.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Splice the values of `B` into `A` on a finite set of physical links. -/
noncomputable def CompactOrientedGaugeWilsonSystem.replaceLinks
    (L : CompactOrientedGaugeWilsonSystem)
    (A B : L.Configuration)
    (s : Finset L.geometry.Edge) : L.Configuration := by
  classical
  exact fun e => if e ∈ s then B e else A e

@[simp] theorem compact_oriented_replaceLinks_empty
    (L : CompactOrientedGaugeWilsonSystem)
    (A B : L.Configuration) :
    L.replaceLinks A B ∅ = A := by
  funext e
  simp [CompactOrientedGaugeWilsonSystem.replaceLinks]

@[simp] theorem compact_oriented_replaceLinks_univ
    (L : CompactOrientedGaugeWilsonSystem)
    (A B : L.Configuration) :
    L.replaceLinks A B Finset.univ = B := by
  classical
  funext e
  simp [CompactOrientedGaugeWilsonSystem.replaceLinks]

/-- Adding one link to the splice set changes no other physical link. -/
theorem compact_oriented_replaceLinks_insert_agreeOffLink
    (L : CompactOrientedGaugeWilsonSystem)
    (A B : L.Configuration)
    (s : Finset L.geometry.Edge)
    (source : L.geometry.Edge) :
    L.AgreeOffLink
      (L.replaceLinks A B (insert source s))
      (L.replaceLinks A B s)
      source := by
  classical
  intro e he
  simp [CompactOrientedGaugeWilsonSystem.replaceLinks, he]

/-- A linkwise variation profile controls the global oscillation by the sum of
its physical-link variations. -/
theorem continuous_compact_oriented_linkVariationBound_globalOscillation_le_sum
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (F : C.base.Configuration → ℝ)
    (P : ContinuousCompactOrientedGaugeWilsonLinkVariationBound C F)
    (A B : C.base.Configuration) :
    |F A - F B| ≤ ∑ e : C.base.geometry.Edge, P.variation e := by
  classical
  have hSplice :
      ∀ s : Finset C.base.geometry.Edge,
        |F (C.base.replaceLinks A B s) - F A| ≤
          ∑ e ∈ s, P.variation e := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simp
    | @insert source s hsource ih =>
        calc
          |F (C.base.replaceLinks A B (insert source s)) - F A| ≤
              |F (C.base.replaceLinks A B (insert source s)) -
                F (C.base.replaceLinks A B s)| +
              |F (C.base.replaceLinks A B s) - F A| :=
            abs_sub_le _ _ _
          _ ≤ P.variation source + ∑ e ∈ s, P.variation e := by
            exact add_le_add
              (P.variation_bound source
                (C.base.replaceLinks A B (insert source s))
                (C.base.replaceLinks A B s)
                (compact_oriented_replaceLinks_insert_agreeOffLink
                  C.base A B s source))
              ih
          _ = ∑ e ∈ insert source s, P.variation e := by
            simp [Finset.sum_insert, hsource]
  have hAll := hSplice (Finset.univ : Finset C.base.geometry.Edge)
  simpa [abs_sub_comm] using hAll

/-- The same global oscillation bound specialized to the centered variation
profiles used by the current Dobrushin/Feller route. -/
theorem continuous_compact_oriented_centeredVariationProfile_globalOscillation_le_sum
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (P : ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile C O)
    (A B : C.base.Configuration) :
    |O A - O B| ≤ ∑ e : C.base.geometry.Edge, P.variation e := by
  let Q : ContinuousCompactOrientedGaugeWilsonLinkVariationBound C
      (fun X => O X) :=
    { variation := P.variation
      variation_nonneg := P.variation_nonneg
      variation_bound := P.variation_bound }
  simpa [Q] using
    (continuous_compact_oriented_linkVariationBound_globalOscillation_le_sum
      C (fun X => O X) Q A B)

/-- The actual finite-volume Wilson Gibbs covariance is controlled by the total
centered physical-link variation of the right observable. -/
theorem continuous_compact_oriented_gibbsCovarianceReal_abs_le_norm_mul_sum_centeredVariation
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (F O : BoundedContinuousFunction C.base.Configuration ℝ)
    (P : ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile C O) :
    |C.gibbsCovarianceReal (fun A => F A) (fun A => O A)| ≤
      ‖F‖ * ∑ e : C.base.geometry.Edge, P.variation e := by
  apply
    continuous_compact_oriented_gibbsCovarianceReal_abs_le_norm_mul_globalOscillation
      C F O (∑ e : C.base.geometry.Edge, P.variation e)
  intro A B
  exact
    continuous_compact_oriented_centeredVariationProfile_globalOscillation_le_sum
      C O P A B

end

end MathlibAnalytic
end MGAP4D
