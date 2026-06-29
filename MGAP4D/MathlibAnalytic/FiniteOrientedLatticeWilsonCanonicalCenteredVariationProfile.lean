import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonCanonicalFiberExtrema

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

noncomputable def FiniteOrientedLatticeWilsonSystem.fiberObservableRanges
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (e : L.Edge) : Finset ℝ := by
  classical
  letI : Fintype L.Configuration := Fintype.ofFinite L.Configuration
  exact Finset.univ.image (fun A : L.Configuration =>
    L.fiberObservableRange f A e)

theorem finite_oriented_fiberObservableRanges_nonempty
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (e : L.Edge) :
    (L.fiberObservableRanges f e).Nonempty := by
  classical
  refine ⟨L.fiberObservableRange f default e, ?_⟩
  simp [FiniteOrientedLatticeWilsonSystem.fiberObservableRanges]

noncomputable def FiniteOrientedLatticeWilsonSystem.canonicalLinkVariation
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (e : L.Edge) : ℝ :=
  (L.fiberObservableRanges f e).max'
    (finite_oriented_fiberObservableRanges_nonempty L f e)

theorem finite_oriented_fiberObservableRange_le_canonicalLinkVariation
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration)
    (e : L.Edge) :
    L.fiberObservableRange f A e ≤ L.canonicalLinkVariation f e := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.canonicalLinkVariation
  apply Finset.le_max'
  simp [FiniteOrientedLatticeWilsonSystem.fiberObservableRanges]

theorem finite_oriented_canonicalLinkVariation_nonneg
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (e : L.Edge) :
    0 ≤ L.canonicalLinkVariation f e :=
  le_trans
    (finite_oriented_fiberObservableRange_nonneg L f default e)
    (finite_oriented_fiberObservableRange_le_canonicalLinkVariation
      L f default e)

theorem finite_oriented_canonicalLinkVariation_difference_abs_le
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (e : L.Edge)
    (A B : L.Configuration)
    (hAgree : L.AgreeOffLink A B e) :
    |f A - f B| ≤ L.canonicalLinkVariation f e := by
  have hLocal :
      |f A - f B| ≤ L.fiberObservableRange f A e := by
    simpa [finite_oriented_replaceLink_current,
      finite_oriented_replaceLink_right_of_agreeOffLink L A B e hAgree] using
      (finite_oriented_fiberObservable_difference_abs_le_range
        L f A e (A e) (B e))
  exact le_trans hLocal
    (finite_oriented_fiberObservableRange_le_canonicalLinkVariation
      L f A e)

theorem finite_oriented_fiberObservable_abs_sub_center_le_half_canonicalVariation
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration)
    (e : L.Edge)
    (g : L.Gauge) :
    |f (L.replaceLink A e g) - L.fiberObservableCenter f A e| ≤
      L.canonicalLinkVariation f e / 2 := by
  calc
    |f (L.replaceLink A e g) - L.fiberObservableCenter f A e| ≤
        L.fiberObservableRange f A e / 2 :=
      finite_oriented_fiberObservable_abs_sub_center_le_half_range
        L f A e g
    _ ≤ L.canonicalLinkVariation f e / 2 := by
      linarith [finite_oriented_fiberObservableRange_le_canonicalLinkVariation
        L f A e]

noncomputable def
    FiniteOrientedLatticeWilsonSystem.canonicalCenteredVariationProfile
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    FiniteOrientedLatticeWilsonCenteredVariationProfile L f := by
  refine
    { variation := L.canonicalLinkVariation f
      variation_nonneg := finite_oriented_canonicalLinkVariation_nonneg L f
      variation_bound := ?_
      fiberCenter := L.fiberObservableCenter f
      fiber_radius_bound := ?_ }
  · intro e A B hAgree
    exact finite_oriented_canonicalLinkVariation_difference_abs_le
      L f e A B hAgree
  · intro A e g
    exact finite_oriented_fiberObservable_abs_sub_center_le_half_canonicalVariation
      L f A e g

end
end MathlibAnalytic
end MGAP4D
