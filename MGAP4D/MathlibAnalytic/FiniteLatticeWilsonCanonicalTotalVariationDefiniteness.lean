import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonCanonicalVariationMinimality
import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonCanonicalVariationDefiniteness
import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonDobrushinTotalVariationContraction

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The exact total single-link oscillation of a finite Wilson observable. -/
def FiniteLatticeWilsonSystem.canonicalTotalVariation
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ) : ℝ :=
  finiteLatticeWilsonTotalVariation (L.canonicalLinkVariation f)

/-- Canonical total variation is nonnegative. -/
theorem finite_lattice_canonicalTotalVariation_nonneg
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    0 ≤ L.canonicalTotalVariation f := by
  unfold FiniteLatticeWilsonSystem.canonicalTotalVariation
    finiteLatticeWilsonTotalVariation
  exact Finset.sum_nonneg fun e _he =>
    finite_lattice_canonicalLinkVariation_nonneg L f e

/-- Constant observables have zero canonical link variation. -/
theorem finite_lattice_canonicalLinkVariation_const_eq_zero
    (L : FiniteLatticeWilsonSystem)
    (c : ℝ)
    (e : L.Edge) :
    L.canonicalLinkVariation (fun _ : L.Configuration => c) e = 0 := by
  let P : FiniteLatticeWilsonLinkVariationBound L
      (fun _ : L.Configuration => c) :=
    { variation := fun _ => 0
      variation_nonneg := fun _ => le_rfl
      variation_bound := by
        intro source A B hAgree
        simp }
  exact le_antisymm
    (finite_lattice_canonicalLinkVariation_le_linkVariationBound
      L (fun _ : L.Configuration => c) P e)
    (finite_lattice_canonicalLinkVariation_nonneg
      L (fun _ : L.Configuration => c) e)

/-- Constant observables have zero canonical total variation. -/
theorem finite_lattice_canonicalTotalVariation_const_eq_zero
    (L : FiniteLatticeWilsonSystem)
    (c : ℝ) :
    L.canonicalTotalVariation (fun _ : L.Configuration => c) = 0 := by
  unfold FiniteLatticeWilsonSystem.canonicalTotalVariation
    finiteLatticeWilsonTotalVariation
  apply Finset.sum_eq_zero
  intro e _he
  exact finite_lattice_canonicalLinkVariation_const_eq_zero L c e

/-- Vanishing canonical total variation forces every link variation to vanish. -/
theorem finite_lattice_all_canonicalLinkVariations_eq_zero_of_total_eq_zero
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (hTotal : L.canonicalTotalVariation f = 0) :
    ∀ e : L.Edge, L.canonicalLinkVariation f e = 0 := by
  intro e
  unfold FiniteLatticeWilsonSystem.canonicalTotalVariation
    finiteLatticeWilsonTotalVariation at hTotal
  have hEach :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun e' (_he' : e' ∈ (Finset.univ : Finset L.Edge)) =>
        finite_lattice_canonicalLinkVariation_nonneg L f e')).mp hTotal
  exact hEach e (Finset.mem_univ e)

/-- Canonical total variation vanishes exactly on constant observables. -/
theorem finite_lattice_canonicalTotalVariation_eq_zero_iff_const
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    L.canonicalTotalVariation f = 0 ↔
      f = fun _ : L.Configuration => f default := by
  constructor
  · intro hTotal
    exact finite_lattice_observable_eq_const_of_all_canonicalVariations_eq_zero
      L f
      (finite_lattice_all_canonicalLinkVariations_eq_zero_of_total_eq_zero
        L f hTotal)
  · intro hConst
    rw [hConst]
    exact finite_lattice_canonicalTotalVariation_const_eq_zero
      L (f default)

/-- On the Gibbs-centered sector, canonical total variation is positive
definite. -/
theorem finite_lattice_centered_observable_eq_zero_of_canonicalTotalVariation_eq_zero
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (hMean : L.gibbsExpectationReal f = 0)
    (hTotal : L.canonicalTotalVariation f = 0) :
    f = 0 := by
  exact
    finite_lattice_centered_observable_eq_zero_of_all_canonicalVariations_eq_zero
      L f hMean
      (finite_lattice_all_canonicalLinkVariations_eq_zero_of_total_eq_zero
        L f hTotal)

end

end MathlibAnalytic
end MGAP4D
