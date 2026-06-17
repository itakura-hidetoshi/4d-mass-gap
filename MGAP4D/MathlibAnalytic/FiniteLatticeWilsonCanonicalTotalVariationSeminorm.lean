import Mathlib.Analysis.Seminorm
import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonCanonicalTotalVariationHomogeneity

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The exact total single-link oscillation bundled as a real seminorm on the
finite Wilson observable space. -/
noncomputable def FiniteLatticeWilsonSystem.canonicalTotalVariationSeminorm
    (L : FiniteLatticeWilsonSystem) :
    Seminorm ℝ (L.Configuration → ℝ) :=
  Seminorm.of
    L.canonicalTotalVariation
    (finite_lattice_canonicalTotalVariation_add_le L)
    (by
      intro c f
      simpa only [Real.norm_eq_abs] using
        (finite_lattice_canonicalTotalVariation_smul L c f))

@[simp] theorem finite_lattice_canonicalTotalVariationSeminorm_apply
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    L.canonicalTotalVariationSeminorm f =
      L.canonicalTotalVariation f :=
  rfl

/-- The kernel of the canonical seminorm consists exactly of constant finite
Wilson observables. -/
theorem finite_lattice_canonicalTotalVariationSeminorm_eq_zero_iff_const
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    L.canonicalTotalVariationSeminorm f = 0 ↔
      f = fun _ : L.Configuration => f default := by
  simpa only [finite_lattice_canonicalTotalVariationSeminorm_apply] using
    (finite_lattice_canonicalTotalVariation_eq_zero_iff_const L f)

/-- On the Gibbs-centered sector the canonical seminorm is definite. -/
theorem finite_lattice_centered_eq_zero_of_canonicalTotalVariationSeminorm_eq_zero
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (hMean : L.gibbsExpectationReal f = 0)
    (hSeminorm : L.canonicalTotalVariationSeminorm f = 0) :
    f = 0 := by
  apply finite_lattice_centered_observable_eq_zero_of_canonicalTotalVariation_eq_zero
    L f hMean
  simpa only [finite_lattice_canonicalTotalVariationSeminorm_apply] using hSeminorm

end

end MathlibAnalytic
end MGAP4D
