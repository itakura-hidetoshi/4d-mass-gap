import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonCanonicalTotalVariationDefiniteness

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Canonical link variation is subadditive. -/
theorem finite_lattice_canonicalLinkVariation_add_le
    (L : FiniteLatticeWilsonSystem)
    (f g : L.Configuration → ℝ)
    (e : L.Edge) :
    L.canonicalLinkVariation (f + g) e ≤
      L.canonicalLinkVariation f e + L.canonicalLinkVariation g e := by
  let P : FiniteLatticeWilsonLinkVariationBound L (f + g) :=
    { variation := fun source =>
        L.canonicalLinkVariation f source +
          L.canonicalLinkVariation g source
      variation_nonneg := by
        intro source
        exact add_nonneg
          (finite_lattice_canonicalLinkVariation_nonneg L f source)
          (finite_lattice_canonicalLinkVariation_nonneg L g source)
      variation_bound := by
        intro source A B hAgree
        change |(f A + g A) - (f B + g B)| ≤
          L.canonicalLinkVariation f source +
            L.canonicalLinkVariation g source
        calc
          |(f A + g A) - (f B + g B)| =
              |(f A - f B) + (g A - g B)| := by
            congr 1
            ring
          _ ≤ |f A - f B| + |g A - g B| := abs_add _ _
          _ ≤ L.canonicalLinkVariation f source +
              L.canonicalLinkVariation g source :=
            add_le_add
              (finite_lattice_canonicalLinkVariation_difference_abs_le
                L f source A B hAgree)
              (finite_lattice_canonicalLinkVariation_difference_abs_le
                L g source A B hAgree) }
  exact finite_lattice_canonicalLinkVariation_le_linkVariationBound
    L (f + g) P e

/-- Canonical total variation satisfies the triangle inequality. -/
theorem finite_lattice_canonicalTotalVariation_add_le
    (L : FiniteLatticeWilsonSystem)
    (f g : L.Configuration → ℝ) :
    L.canonicalTotalVariation (f + g) ≤
      L.canonicalTotalVariation f + L.canonicalTotalVariation g := by
  unfold FiniteLatticeWilsonSystem.canonicalTotalVariation
    finiteLatticeWilsonTotalVariation
  calc
    (∑ e : L.Edge, L.canonicalLinkVariation (f + g) e) ≤
        ∑ e : L.Edge,
          (L.canonicalLinkVariation f e +
            L.canonicalLinkVariation g e) := by
      apply Finset.sum_le_sum
      intro e _he
      exact finite_lattice_canonicalLinkVariation_add_le L f g e
    _ = (∑ e : L.Edge, L.canonicalLinkVariation f e) +
        ∑ e : L.Edge, L.canonicalLinkVariation g e := by
      rw [Finset.sum_add_distrib]

/-- Canonical link variation is invariant under negation. -/
theorem finite_lattice_canonicalLinkVariation_neg
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (e : L.Edge) :
    L.canonicalLinkVariation (-f) e =
      L.canonicalLinkVariation f e := by
  have hForward :
      L.canonicalLinkVariation (-f) e ≤
        L.canonicalLinkVariation f e := by
    let P : FiniteLatticeWilsonLinkVariationBound L (-f) :=
      { variation := L.canonicalLinkVariation f
        variation_nonneg := finite_lattice_canonicalLinkVariation_nonneg L f
        variation_bound := by
          intro source A B hAgree
          change |(-f A) - (-f B)| ≤
            L.canonicalLinkVariation f source
          calc
            |(-f A) - (-f B)| = |f A - f B| := by
              rw [neg_sub_neg, abs_sub_comm]
            _ ≤ L.canonicalLinkVariation f source :=
              finite_lattice_canonicalLinkVariation_difference_abs_le
                L f source A B hAgree }
    exact finite_lattice_canonicalLinkVariation_le_linkVariationBound
      L (-f) P e
  have hBackward :
      L.canonicalLinkVariation f e ≤
        L.canonicalLinkVariation (-f) e := by
    let P : FiniteLatticeWilsonLinkVariationBound L f :=
      { variation := L.canonicalLinkVariation (-f)
        variation_nonneg :=
          finite_lattice_canonicalLinkVariation_nonneg L (-f)
        variation_bound := by
          intro source A B hAgree
          have hNeg :=
            finite_lattice_canonicalLinkVariation_difference_abs_le
              L (-f) source A B hAgree
          change |f A - f B| ≤
            L.canonicalLinkVariation (-f) source
          simpa only [Pi.neg_apply, neg_sub_neg, abs_sub_comm] using hNeg }
    exact finite_lattice_canonicalLinkVariation_le_linkVariationBound
      L f P e
  exact le_antisymm hForward hBackward

/-- Canonical total variation is invariant under negation. -/
theorem finite_lattice_canonicalTotalVariation_neg
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    L.canonicalTotalVariation (-f) = L.canonicalTotalVariation f := by
  unfold FiniteLatticeWilsonSystem.canonicalTotalVariation
    finiteLatticeWilsonTotalVariation
  apply Finset.sum_congr rfl
  intro e _he
  exact finite_lattice_canonicalLinkVariation_neg L f e

end

end MathlibAnalytic
end MGAP4D
