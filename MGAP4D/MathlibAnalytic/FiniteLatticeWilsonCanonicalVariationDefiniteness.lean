import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonCanonicalVariationDefinitenessV2

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Patch into `A` the values of `B` on the selected finite set of links. -/
def FiniteLatticeWilsonSystem.configurationPatch
    (L : FiniteLatticeWilsonSystem)
    (A B : L.Configuration)
    (s : Finset L.Edge) : L.Configuration :=
  fun e => if e ∈ s then B e else A e

@[simp] theorem finite_lattice_configurationPatch_empty
    (L : FiniteLatticeWilsonSystem)
    (A B : L.Configuration) :
    L.configurationPatch A B ∅ = A := by
  funext e
  simp [FiniteLatticeWilsonSystem.configurationPatch]

@[simp] theorem finite_lattice_configurationPatch_univ
    (L : FiniteLatticeWilsonSystem)
    (A B : L.Configuration) :
    L.configurationPatch A B Finset.univ = B := by
  funext e
  simp [FiniteLatticeWilsonSystem.configurationPatch]

/-- Adding one selected link to a patch changes no other link. -/
theorem finite_lattice_configurationPatch_agreeOffLink_insert
    (L : FiniteLatticeWilsonSystem)
    (A B : L.Configuration)
    (s : Finset L.Edge)
    (e : L.Edge) :
    L.AgreeOffLink
      (L.configurationPatch A B s)
      (L.configurationPatch A B (insert e s)) e := by
  intro e' hne
  by_cases hs : e' ∈ s
  · simp [FiniteLatticeWilsonSystem.configurationPatch, hs]
  · have hInsert : e' ∉ insert e s := by
      simp [hne, hs]
    simp [FiniteLatticeWilsonSystem.configurationPatch, hs, hInsert]

/-- Zero canonical variation at one link forces invariance under every change
supported on that link. -/
theorem finite_lattice_observable_eq_of_agreeOffLink_of_canonicalVariation_eq_zero
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (e : L.Edge)
    (A B : L.Configuration)
    (hAgree : L.AgreeOffLink A B e)
    (hZero : L.canonicalLinkVariation f e = 0) :
    f A = f B := by
  have hBound : |f A - f B| ≤ 0 := by
    simpa [hZero] using
      (finite_lattice_canonicalLinkVariation_difference_abs_le
        L f e A B hAgree)
  have hAbs : |f A - f B| = 0 :=
    le_antisymm hBound (abs_nonneg _)
  exact sub_eq_zero.mp (abs_eq_zero.mp hAbs)

end

end MathlibAnalytic
end MGAP4D
