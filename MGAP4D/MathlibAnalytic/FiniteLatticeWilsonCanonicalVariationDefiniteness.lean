import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonCanonicalCenteredVariationProfile

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

end

end MathlibAnalytic
end MGAP4D
