import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonCanonicalCenteredVariationProfile

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

theorem finite_oriented_fiberObservableRange_le_linkVariationBound
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (P : FiniteOrientedLatticeWilsonLinkVariationBound L f)
    (A : L.Configuration)
    (e : L.Edge) :
    L.fiberObservableRange f A e ≤ P.variation e := by
  classical
  have hMaxExists :
      ∃ g : L.Gauge,
        f (L.replaceLink A e g) = L.fiberObservableMax f A e := by
    have hMem :
        L.fiberObservableMax f A e ∈ L.fiberObservableValues f A e := by
      unfold FiniteOrientedLatticeWilsonSystem.fiberObservableMax
      exact Finset.max'_mem _ _
    simpa [FiniteOrientedLatticeWilsonSystem.fiberObservableValues] using hMem
  have hMinExists :
      ∃ g : L.Gauge,
        f (L.replaceLink A e g) = L.fiberObservableMin f A e := by
    have hMem :
        L.fiberObservableMin f A e ∈ L.fiberObservableValues f A e := by
      unfold FiniteOrientedLatticeWilsonSystem.fiberObservableMin
      exact Finset.min'_mem _ _
    simpa [FiniteOrientedLatticeWilsonSystem.fiberObservableValues] using hMem
  rcases hMaxExists with ⟨gMax, hMax⟩
  rcases hMinExists with ⟨gMin, hMin⟩
  have hAgree :
      L.AgreeOffLink
        (L.replaceLink A e gMax)
        (L.replaceLink A e gMin) e := by
    intro e' hne
    simp [FiniteOrientedLatticeWilsonSystem.replaceLink, hne]
  have hBound :=
    P.variation_bound e
      (L.replaceLink A e gMax)
      (L.replaceLink A e gMin) hAgree
  have hRangeNonneg :=
    finite_oriented_fiberObservableRange_nonneg L f A e
  unfold FiniteOrientedLatticeWilsonSystem.fiberObservableRange at hRangeNonneg ⊢
  calc
    L.fiberObservableMax f A e - L.fiberObservableMin f A e =
        |L.fiberObservableMax f A e - L.fiberObservableMin f A e| :=
      (abs_of_nonneg hRangeNonneg).symm
    _ = |f (L.replaceLink A e gMax) -
          f (L.replaceLink A e gMin)| := by
      rw [hMax, hMin]
    _ ≤ P.variation e := hBound

theorem finite_oriented_canonicalLinkVariation_le_linkVariationBound
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (P : FiniteOrientedLatticeWilsonLinkVariationBound L f)
    (e : L.Edge) :
    L.canonicalLinkVariation f e ≤ P.variation e := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.canonicalLinkVariation
  apply Finset.max'_le
  intro r hr
  have hExists :
      ∃ A : L.Configuration,
        L.fiberObservableRange f A e = r := by
    simpa [FiniteOrientedLatticeWilsonSystem.fiberObservableRanges] using hr
  rcases hExists with ⟨A, rfl⟩
  exact finite_oriented_fiberObservableRange_le_linkVariationBound
    L f P A e

end
end MathlibAnalytic
end MGAP4D
