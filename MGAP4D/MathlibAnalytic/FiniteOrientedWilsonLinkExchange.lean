import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonSingleLinkHeatBathDetailedBalance

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

@[simp] theorem finite_oriented_replaceLink_replaceLink
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge)
    (h g : L.Gauge) :
    L.replaceLink (L.replaceLink A target h) target g =
      L.replaceLink A target g := by
  classical
  funext e
  by_cases he : e = target
  · subst e
    simp
  · simp [FiniteOrientedLatticeWilsonSystem.replaceLink, he]

noncomputable def FiniteOrientedLatticeWilsonSystem.singleLinkUpdateSwapEquiv
    (L : FiniteOrientedLatticeWilsonSystem)
    (target : L.Edge) :
    (L.Configuration × L.Gauge) ≃ (L.Configuration × L.Gauge) where
  toFun := fun x => (L.replaceLink x.1 target x.2, x.1 target)
  invFun := fun x => (L.replaceLink x.1 target x.2, x.1 target)
  left_inv := by
    rintro ⟨A, g⟩
    apply Prod.ext
    · change L.replaceLink (L.replaceLink A target g) target (A target) = A
      rw [finite_oriented_replaceLink_replaceLink,
        finite_oriented_replaceLink_current]
    · simp
  right_inv := by
    rintro ⟨A, g⟩
    apply Prod.ext
    · change L.replaceLink (L.replaceLink A target g) target (A target) = A
      rw [finite_oriented_replaceLink_replaceLink,
        finite_oriented_replaceLink_current]
    · simp

@[simp] theorem finite_oriented_singleLinkUpdateSwap_first_roundTrip
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge)
    (g : L.Gauge) :
    L.replaceLink (L.replaceLink A target g) target (A target) = A := by
  rw [finite_oriented_replaceLink_replaceLink,
    finite_oriented_replaceLink_current]

end
end MathlibAnalytic
end MGAP4D
