import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonCanonicalCenteredVariationProfile

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Every declared link-variation bound dominates the exact range of each
single-link fiber. -/
theorem finite_lattice_fiberObservableRange_le_linkVariationBound
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (P : FiniteLatticeWilsonLinkVariationBound L f)
    (A : L.Configuration)
    (e : L.Edge) :
    L.fiberObservableRange f A e ≤ P.variation e := by
  classical
  have hMaxExists :
      ∃ g : L.Gauge,
        f (L.replaceLink A e g) = L.fiberObservableMax f A e := by
    have hMem :
        L.fiberObservableMax f A e ∈ L.fiberObservableValues f A e := by
      unfold FiniteLatticeWilsonSystem.fiberObservableMax
      exact Finset.max'_mem _ _
    simpa [FiniteLatticeWilsonSystem.fiberObservableValues] using hMem
  have hMinExists :
      ∃ g : L.Gauge,
        f (L.replaceLink A e g) = L.fiberObservableMin f A e := by
    have hMem :
        L.fiberObservableMin f A e ∈ L.fiberObservableValues f A e := by
      unfold FiniteLatticeWilsonSystem.fiberObservableMin
      exact Finset.min'_mem _ _
    simpa [FiniteLatticeWilsonSystem.fiberObservableValues] using hMem
  rcases hMaxExists with ⟨gMax, hMax⟩
  rcases hMinExists with ⟨gMin, hMin⟩
  have hAgree :
      L.AgreeOffLink
        (L.replaceLink A e gMax)
        (L.replaceLink A e gMin) e := by
    intro e' hne
    simp [FiniteLatticeWilsonSystem.replaceLink, hne]
  have hBound :=
    P.variation_bound e
      (L.replaceLink A e gMax)
      (L.replaceLink A e gMin) hAgree
  have hRangeNonneg :=
    finite_lattice_fiberObservableRange_nonneg L f A e
  unfold FiniteLatticeWilsonSystem.fiberObservableRange at hRangeNonneg ⊢
  calc
    L.fiberObservableMax f A e - L.fiberObservableMin f A e =
        |L.fiberObservableMax f A e - L.fiberObservableMin f A e| :=
      (abs_of_nonneg hRangeNonneg).symm
    _ = |f (L.replaceLink A e gMax) -
          f (L.replaceLink A e gMin)| := by
      rw [hMax, hMin]
    _ ≤ P.variation e := hBound

/-- The canonical link variation is the least pointwise link-variation bound:
it lies below every proof-relevant variation profile for the same observable. -/
theorem finite_lattice_canonicalLinkVariation_le_linkVariationBound
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (P : FiniteLatticeWilsonLinkVariationBound L f)
    (e : L.Edge) :
    L.canonicalLinkVariation f e ≤ P.variation e := by
  classical
  unfold FiniteLatticeWilsonSystem.canonicalLinkVariation
  apply Finset.max'_le
  intro r hr
  have hExists :
      ∃ A : L.Configuration,
        L.fiberObservableRange f A e = r := by
    simpa [FiniteLatticeWilsonSystem.fiberObservableRanges] using hr
  rcases hExists with ⟨A, rfl⟩
  exact finite_lattice_fiberObservableRange_le_linkVariationBound
    L f P A e

end

end MathlibAnalytic
end MGAP4D
