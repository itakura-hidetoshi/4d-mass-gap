import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonPlaquetteObservableVariation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A proof-relevant physical-link oscillation bound for an orientation-correct
finite Wilson observable. -/
structure FiniteOrientedLatticeWilsonLinkVariationBound
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ) where
  variation : L.Edge → ℝ
  variation_nonneg : ∀ e : L.Edge, 0 ≤ variation e
  variation_bound :
    ∀ (e : L.Edge) (A B : L.Configuration),
      L.AgreeOffLink A B e → |f A - f B| ≤ variation e

/-- A physical-link oscillation profile with a center on every one-link fiber.
The half-variation radius is the normalization needed by total-variation
comparison estimates. -/
structure FiniteOrientedLatticeWilsonCenteredVariationProfile
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    extends FiniteOrientedLatticeWilsonLinkVariationBound L f where
  fiberCenter : L.Configuration → L.Edge → ℝ
  fiber_radius_bound :
    ∀ (A : L.Configuration) (e : L.Edge) (g : L.Gauge),
      |f (L.replaceLink A e g) - fiberCenter A e| ≤ variation e / 2

/-- Canonical fiber center for one unit-bounded plaquette observable. On a
boundary link use the midpoint `1/2`; off the boundary the observable is
constant along the fiber, so use its original value. -/
def FiniteOrientedLatticeWilsonSystem.plaquetteObservableFiberCenter
    (L : FiniteOrientedLatticeWilsonSystem)
    (p : L.Plaquette)
    (A : L.Configuration)
    (source : L.Edge) : ℝ := by
  classical
  exact if L.PlaquetteTouchesEdge p source then 1 / 2 else
    L.plaquetteObservable p A

/-- A unit-bounded plaquette observable lies within radius `1/2` of the midpoint
on every boundary-link fiber. -/
theorem finite_oriented_plaquetteObservable_boundaryFiber_radius
    (L : FiniteOrientedLatticeWilsonSystem)
    (U : FiniteOrientedLatticeWilsonPlaquetteEnergyUnitBound L)
    (p : L.Plaquette)
    (A : L.Configuration)
    (source : L.Edge)
    (g : L.Gauge) :
    |L.plaquetteObservable p (L.replaceLink A source g) - (1 / 2 : ℝ)| ≤
      1 / 2 := by
  have h0 : 0 ≤ L.plaquetteObservable p (L.replaceLink A source g) :=
    L.plaquetteEnergy_nonneg _
  have h1 : L.plaquetteObservable p (L.replaceLink A source g) ≤ 1 :=
    U.le_one _
  rw [abs_le]
  constructor <;> linarith

/-- Replacing a non-boundary link leaves a plaquette observable equal to its
original value. -/
theorem finite_oriented_plaquetteObservable_replaceLink_eq_of_not_touches
    (L : FiniteOrientedLatticeWilsonSystem)
    (p : L.Plaquette)
    (A : L.Configuration)
    (source : L.Edge)
    (g : L.Gauge)
    (hNotTouch : ¬ L.PlaquetteTouchesEdge p source) :
    L.plaquetteObservable p (L.replaceLink A source g) =
      L.plaquetteObservable p A := by
  apply finite_oriented_plaquetteObservable_eq_of_agreeOffLink_of_not_touches
    L p (L.replaceLink A source g) A source
  · intro e he
    exact finite_oriented_replaceLink_of_ne L A source e g he
  · exact hNotTouch

/-- The exact plaquette-boundary variation indicator together with the
piecewise midpoint/constant center gives a centered variation profile. -/
noncomputable def
    FiniteOrientedLatticeWilsonPlaquetteEnergyUnitBound.centeredVariationProfile
    {L : FiniteOrientedLatticeWilsonSystem}
    (U : FiniteOrientedLatticeWilsonPlaquetteEnergyUnitBound L)
    (p : L.Plaquette) :
    FiniteOrientedLatticeWilsonCenteredVariationProfile L
      (L.plaquetteObservable p) :=
  { variation := L.plaquetteObservableLinkVariation p
    variation_nonneg :=
      finite_oriented_plaquetteObservableLinkVariation_nonneg L p
    variation_bound := by
      intro source A B hAgree
      exact finite_oriented_plaquetteObservable_variation_bound
        L U p source A B hAgree
    fiberCenter := L.plaquetteObservableFiberCenter p
    fiber_radius_bound := by
      classical
      intro A source g
      by_cases hTouch : L.PlaquetteTouchesEdge p source
      · simpa [FiniteOrientedLatticeWilsonSystem.plaquetteObservableFiberCenter,
          FiniteOrientedLatticeWilsonSystem.plaquetteObservableLinkVariation,
          hTouch] using
          finite_oriented_plaquetteObservable_boundaryFiber_radius
            L U p A source g
      · have hEq :=
          finite_oriented_plaquetteObservable_replaceLink_eq_of_not_touches
            L p A source g hTouch
        simp [FiniteOrientedLatticeWilsonSystem.plaquetteObservableFiberCenter,
          FiniteOrientedLatticeWilsonSystem.plaquetteObservableLinkVariation,
          hTouch, hEq] }

/-- The periodic `Z₂` selected plaquette observable carries the explicit
centered profile supported on its four physical boundary links. -/
noncomputable def z2PeriodicHypercubicOrientedPlaquetteCenteredVariationProfile
    (n : ℕ) [NeZero n]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (p : PeriodicHypercubicPlaquette n) :
    FiniteOrientedLatticeWilsonCenteredVariationProfile
      (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
      ((z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta).plaquetteObservable p) :=
  (z2PeriodicHypercubicOrientedPlaquetteEnergyUnitBound n beta hBeta)
    |>.centeredVariationProfile p

/-- The concrete centered profile variation is exactly the periodic physical
boundary indicator. -/
theorem z2PeriodicHypercubicOrientedPlaquetteCenteredVariationProfile_variation
    (n : ℕ) [NeZero n]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (p : PeriodicHypercubicPlaquette n)
    (source : PeriodicHypercubicEdge n) :
    (z2PeriodicHypercubicOrientedPlaquetteCenteredVariationProfile
      n beta hBeta p).variation source =
        periodicHypercubicPlaquetteObservableLinkVariation n p source := by
  classical
  rfl

end

end MathlibAnalytic
end MGAP4D
