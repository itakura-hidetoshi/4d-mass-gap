import MGAP4D.MathlibAnalytic.FiniteWilsonPairingCore

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Exchanging the old and resampled value at one link is an involution. -/
noncomputable def FiniteLatticeWilsonSystem.singleLinkUpdateSwapEquiv
    (L : FiniteLatticeWilsonSystem) (e : L.Edge) :
    (L.Configuration × L.Gauge) ≃ (L.Configuration × L.Gauge) where
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

end

end MathlibAnalytic
end MGAP4D
