import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonSingleLinkHeatBathDetailedBalance
import Mathlib.Data.Fintype.BigOperators

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The Gibbs-weighted real bilinear pairing on finite Wilson observables. -/
def FiniteLatticeWilsonSystem.gibbsPairingReal
    (L : FiniteLatticeWilsonSystem)
    (f g : L.Configuration → ℝ) : ℝ := by
  classical
  exact ∑ A : L.Configuration, L.gibbsProbabilityReal A * f A * g A

/-- The finite Wilson Gibbs pairing is symmetric. -/
theorem finite_lattice_gibbsPairingReal_symm
    (L : FiniteLatticeWilsonSystem)
    (f g : L.Configuration → ℝ) :
    L.gibbsPairingReal f g = L.gibbsPairingReal g f := by
  classical
  unfold FiniteLatticeWilsonSystem.gibbsPairingReal
  apply Finset.sum_congr rfl
  intro A _hA
  ring

/-- Swapping the old and resampled values of one link is an involutive
permutation of configuration--gauge pairs. -/
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

/-- Detailed balance reindexes the full finite update sum by the update-swap
involution. -/
theorem finite_lattice_singleLinkHeatBath_reversible_double_sum
    (L : FiniteLatticeWilsonSystem)
    (e : L.Edge) (f g : L.Configuration → ℝ) :
    (∑ A : L.Configuration, ∑ h : L.Gauge,
      L.gibbsProbabilityReal A *
        (L.singleLinkConditionalPMF A e h).toReal *
        f (L.replaceLink A e h) * g A) =
      ∑ A : L.Configuration, ∑ h : L.Gauge,
        L.gibbsProbabilityReal A *
          (L.singleLinkConditionalPMF A e h).toReal *
          f A * g (L.replaceLink A e h) := by
  classical
  rw [← Fintype.sum_prod_type, ← Fintype.sum_prod_type]
  refine Fintype.sum_equiv (L.singleLinkUpdateSwapEquiv e) _ _ ?_
  rintro ⟨A, h⟩
  change L.gibbsProbabilityReal A *
      (L.singleLinkConditionalPMF A e h).toReal *
      f (L.replaceLink A e h) * g A =
    L.gibbsProbabilityReal (L.replaceLink A e h) *
      (L.singleLinkConditionalPMF
        (L.replaceLink A e h) e (A e)).toReal *
      f (L.replaceLink A e h) *
      g (L.replaceLink (L.replaceLink A e h) e (A e))
  rw [finite_lattice_singleLinkHeatBath_detailedBalance_real]
  simp

/-- Exact single-link conditional expectation is self-adjoint for the
Gibbs-weighted pairing. -/
theorem finite_lattice_singleLinkHeatBathProjection_gibbs_selfAdjoint
    (L : FiniteLatticeWilsonSystem)
    (e : L.Edge) (f g : L.Configuration → ℝ) :
    L.gibbsPairingReal
        (L.singleLinkHeatBathProjectionLinearMap e f) g =
      L.gibbsPairingReal f
        (L.singleLinkHeatBathProjectionLinearMap e g) := by
  classical
  unfold FiniteLatticeWilsonSystem.gibbsPairingReal
  change (∑ A : L.Configuration,
      L.gibbsProbabilityReal A *
        (∑ h : L.Gauge,
          (L.singleLinkConditionalPMF A e h).toReal *
            f (L.replaceLink A e h)) * g A) =
    ∑ A : L.Configuration,
      L.gibbsProbabilityReal A * f A *
        (∑ h : L.Gauge,
          (L.singleLinkConditionalPMF A e h).toReal *
            g (L.replaceLink A e h))
  calc
    _ = ∑ A : L.Configuration, ∑ h : L.Gauge,
        L.gibbsProbabilityReal A *
          (L.singleLinkConditionalPMF A e h).toReal *
          f (L.replaceLink A e h) * g A := by
      apply Finset.sum_congr rfl
      intro A _hA
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro h _hh
      ring
    _ = ∑ A : L.Configuration, ∑ h : L.Gauge,
        L.gibbsProbabilityReal A *
          (L.singleLinkConditionalPMF A e h).toReal *
          f A * g (L.replaceLink A e h) :=
      finite_lattice_singleLinkHeatBath_reversible_double_sum L e f g
    _ = _ := by
      apply Finset.sum_congr rfl
      intro A _hA
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _hh
      ring

end

end MathlibAnalytic
end MGAP4D
