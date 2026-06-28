import MGAP4D.MathlibAnalytic.FiniteOrientedWilsonPairingCore

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Exchanging the old and resampled value of one physical link is an
involution on configuration-value pairs. -/
noncomputable def
    FiniteOrientedLatticeWilsonSystem.singleLinkUpdateSwapEquiv
    (L : FiniteOrientedLatticeWilsonSystem)
    (e : L.Edge) :
    (L.Configuration × L.Gauge) ≃
      (L.Configuration × L.Gauge) where
  toFun := fun x => (L.replaceLink x.1 e x.2, x.1 e)
  invFun := fun x => (L.replaceLink x.1 e x.2, x.1 e)
  left_inv := by
    rintro ⟨A, g⟩
    apply Prod.ext
    · simp
    · simp
  right_inv := by
    rintro ⟨A, g⟩
    apply Prod.ext
    · simp
    · simp

/-- The first component of the oriented link-exchange involution restores the
original physical-link configuration. -/
@[simp] theorem finite_oriented_singleLinkUpdateSwap_first_roundTrip
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (e : L.Edge)
    (h : L.Gauge) :
    L.replaceLink (L.replaceLink A e h) e (A e) = A := by
  simpa
    [FiniteOrientedLatticeWilsonSystem.singleLinkUpdateSwapEquiv]
    using congrArg Prod.fst
      ((L.singleLinkUpdateSwapEquiv e).left_inv (A, h))

end

end MathlibAnalytic
end MGAP4D
