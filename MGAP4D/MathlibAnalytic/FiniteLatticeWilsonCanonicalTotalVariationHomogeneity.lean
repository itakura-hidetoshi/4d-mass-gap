import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonCanonicalTotalVariationAlgebra

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Scaling an observable gives the expected upper bound on each canonical link
variation. -/
theorem finite_lattice_canonicalLinkVariation_smul_le
    (L : FiniteLatticeWilsonSystem)
    (c : ℝ)
    (f : L.Configuration → ℝ)
    (e : L.Edge) :
    L.canonicalLinkVariation (c • f) e ≤
      |c| * L.canonicalLinkVariation f e := by
  let P : FiniteLatticeWilsonLinkVariationBound L (c • f) :=
    { variation := fun source =>
        |c| * L.canonicalLinkVariation f source
      variation_nonneg := by
        intro source
        exact mul_nonneg (abs_nonneg c)
          (finite_lattice_canonicalLinkVariation_nonneg L f source)
      variation_bound := by
        intro source A B hAgree
        change |c * f A - c * f B| ≤
          |c| * L.canonicalLinkVariation f source
        calc
          |c * f A - c * f B| = |c| * |f A - f B| := by
            rw [← mul_sub, abs_mul]
          _ ≤ |c| * L.canonicalLinkVariation f source :=
            mul_le_mul_of_nonneg_left
              (finite_lattice_canonicalLinkVariation_difference_abs_le
                L f source A B hAgree)
              (abs_nonneg c) }
  exact finite_lattice_canonicalLinkVariation_le_linkVariationBound
    L (c • f) P e

/-- Canonical link variation is exactly homogeneous under real scalar
multiplication. -/
theorem finite_lattice_canonicalLinkVariation_smul
    (L : FiniteLatticeWilsonSystem)
    (c : ℝ)
    (f : L.Configuration → ℝ)
    (e : L.Edge) :
    L.canonicalLinkVariation (c • f) e =
      |c| * L.canonicalLinkVariation f e := by
  by_cases hc : c = 0
  · subst c
    rw [zero_smul, abs_zero, zero_mul]
    change L.canonicalLinkVariation
      (fun _ : L.Configuration => 0) e = 0
    exact finite_lattice_canonicalLinkVariation_const_eq_zero L 0 e
  · have hForward :=
      finite_lattice_canonicalLinkVariation_smul_le L c f e
    have hInv :
        L.canonicalLinkVariation f e ≤
          |c⁻¹| * L.canonicalLinkVariation (c • f) e := by
      simpa [smul_smul, hc] using
        (finite_lattice_canonicalLinkVariation_smul_le
          L c⁻¹ (c • f) e)
    have hBackward :
        |c| * L.canonicalLinkVariation f e ≤
          L.canonicalLinkVariation (c • f) e := by
      calc
        |c| * L.canonicalLinkVariation f e ≤
            |c| *
              (|c⁻¹| * L.canonicalLinkVariation (c • f) e) :=
          mul_le_mul_of_nonneg_left hInv (abs_nonneg c)
        _ = L.canonicalLinkVariation (c • f) e := by
          rw [abs_inv, ← mul_assoc, mul_inv_cancel₀ (abs_ne_zero.mpr hc),
            one_mul]
    exact le_antisymm hForward hBackward

/-- Canonical total variation is exactly homogeneous under real scalar
multiplication. -/
theorem finite_lattice_canonicalTotalVariation_smul
    (L : FiniteLatticeWilsonSystem)
    (c : ℝ)
    (f : L.Configuration → ℝ) :
    L.canonicalTotalVariation (c • f) =
      |c| * L.canonicalTotalVariation f := by
  unfold FiniteLatticeWilsonSystem.canonicalTotalVariation
    finiteLatticeWilsonTotalVariation
  calc
    (∑ e : L.Edge, L.canonicalLinkVariation (c • f) e) =
        ∑ e : L.Edge, |c| * L.canonicalLinkVariation f e := by
      apply Finset.sum_congr rfl
      intro e _he
      exact finite_lattice_canonicalLinkVariation_smul L c f e
    _ = |c| * ∑ e : L.Edge, L.canonicalLinkVariation f e := by
      rw [Finset.mul_sum]

end

end MathlibAnalytic
end MGAP4D
