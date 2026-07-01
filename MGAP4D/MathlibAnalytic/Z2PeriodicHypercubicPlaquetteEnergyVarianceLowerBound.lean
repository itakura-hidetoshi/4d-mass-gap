import MGAP4D.MathlibAnalytic.FiniteOrientedWilsonTwoPointConditionalVarianceLowerBound
import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicPlaquetteEnergyVariance
import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicSingleLinkConditionalPointLowerBound
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Multiplication by the nontrivial `Z₂` element toggles the `0/1` plaquette
energy, so the squared energy difference is one. -/
theorem z2Gauge_plaquetteEnergy_toggle_sq
    (q : Z2Gauge) :
    ((if q = 1 then (0 : ℝ) else 1) -
        (if z2GaugeNontrivial * q = 1 then (0 : ℝ) else 1)) ^ 2 = 1 := by
  have hNontrivial : z2GaugeNontrivial ≠ 1 := by
    native_decide
  have hSquare : z2GaugeNontrivial * z2GaugeNontrivial = 1 := by
    native_decide
  have hCases : q = 1 ∨ q = z2GaugeNontrivial := by
    fin_cases q
    · left
      native_decide
    · right
      native_decide
  rcases hCases with hq | hq
  · rw [hq]
    simp [hNontrivial]
  · rw [hq]
    simp [hNontrivial, hSquare]

/-- Replacing the first physical boundary link of a periodic plaquette factors
its holonomy into the inserted value and an exterior three-step product. -/
theorem z2PeriodicHypercubic_plaquetteHolonomy_replace_firstEdge
    (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (p : PeriodicHypercubicPlaquette n)
    (A : (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta).Configuration)
    (g : (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta).Gauge) :
    let L := z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta
    let e0 : L.Edge := (p.1, periodicHypercubicPlaquetteFirstAxis p)
    L.plaquetteHolonomy (L.replaceLink A e0 g) p =
      g * L.stepValue A (L.boundary p 1) *
        L.stepValue A (L.boundary p 2) *
        L.stepValue A (L.boundary p 3) := by
  let L := z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta
  let mu := periodicHypercubicPlaquetteFirstAxis p
  let nu := periodicHypercubicPlaquetteSecondAxis p
  let e0 : L.Edge := (p.1, mu)
  change L.plaquetteHolonomy (L.replaceLink A e0 g) p =
    g * L.stepValue A (L.boundary p 1) *
      L.stepValue A (L.boundary p 2) *
      L.stepValue A (L.boundary p 3)
  have hmuNu : mu ≠ nu := periodicHypercubicPlaquette_axes_ne p
  have he1 : (periodicHypercubicShift n p.1 mu, nu) ≠ e0 := by
    intro h
    exact hmuNu (congrArg Prod.snd h).symm
  have he2 : (periodicHypercubicShift n p.1 nu, mu) ≠ e0 := by
    intro h
    exact periodicHypercubicShift_ne_self_of_two_le n hn p.1 nu
      (congrArg Prod.fst h)
  have he3 : (p.1, nu) ≠ e0 := by
    intro h
    exact hmuNu (congrArg Prod.snd h).symm
  have hStep0 :
      L.stepValue (L.replaceLink A e0 g) (L.boundary p 0) = g := by
    change L.replaceLink A e0 g e0 = g
    rw [finite_oriented_replaceLink_same]
  have hStep1 :
      L.stepValue (L.replaceLink A e0 g) (L.boundary p 1) =
        L.stepValue A (L.boundary p 1) := by
    change L.replaceLink A e0 g
        (periodicHypercubicShift n p.1 mu, nu) =
      A (periodicHypercubicShift n p.1 mu, nu)
    exact finite_oriented_replaceLink_of_ne L A e0
      (periodicHypercubicShift n p.1 mu, nu) g he1
  have hStep2 :
      L.stepValue (L.replaceLink A e0 g) (L.boundary p 2) =
        L.stepValue A (L.boundary p 2) := by
    change (L.replaceLink A e0 g
        (periodicHypercubicShift n p.1 nu, mu))⁻¹ =
      (A (periodicHypercubicShift n p.1 nu, mu))⁻¹
    exact congrArg Inv.inv
      (finite_oriented_replaceLink_of_ne L A e0
        (periodicHypercubicShift n p.1 nu, mu) g he2)
  have hStep3 :
      L.stepValue (L.replaceLink A e0 g) (L.boundary p 3) =
        L.stepValue A (L.boundary p 3) := by
    change (L.replaceLink A e0 g (p.1, nu))⁻¹ = (A (p.1, nu))⁻¹
    exact congrArg Inv.inv
      (finite_oriented_replaceLink_of_ne L A e0 (p.1, nu) g he3)
  unfold FiniteOrientedLatticeWilsonSystem.plaquetteHolonomy
  rw [hStep0, hStep1, hStep2, hStep3]

/-- For every exterior configuration, the selected plaquette-energy values
obtained by inserting the two `Z₂` link values differ by squared distance one. -/
theorem z2PeriodicHypercubicPlaquetteEnergyObservable_replace_firstEdge_difference_sq
    (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (p : PeriodicHypercubicPlaquette n)
    (A : (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta).Configuration) :
    let L := z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta
    let e0 : L.Edge := (p.1, periodicHypercubicPlaquetteFirstAxis p)
    (z2PeriodicHypercubicPlaquetteEnergyObservable n beta hBeta p
          (L.replaceLink A e0 1) -
        z2PeriodicHypercubicPlaquetteEnergyObservable n beta hBeta p
          (L.replaceLink A e0 z2GaugeNontrivial)) ^ 2 = 1 := by
  let L := z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta
  let e0 : L.Edge := (p.1, periodicHypercubicPlaquetteFirstAxis p)
  let q : Z2Gauge :=
    L.stepValue A (L.boundary p 1) *
      L.stepValue A (L.boundary p 2) *
      L.stepValue A (L.boundary p 3)
  change (z2PeriodicHypercubicPlaquetteEnergyObservable n beta hBeta p
        (L.replaceLink A e0 1) -
      z2PeriodicHypercubicPlaquetteEnergyObservable n beta hBeta p
        (L.replaceLink A e0 z2GaugeNontrivial)) ^ 2 = 1
  have hHolonomyIdentity :=
    z2PeriodicHypercubic_plaquetteHolonomy_replace_firstEdge
      n hn beta hBeta p A (1 : Z2Gauge)
  change L.plaquetteHolonomy (L.replaceLink A e0 1) p =
    (1 : Z2Gauge) * L.stepValue A (L.boundary p 1) *
      L.stepValue A (L.boundary p 2) *
      L.stepValue A (L.boundary p 3) at hHolonomyIdentity
  have hHolonomyNontrivial :=
    z2PeriodicHypercubic_plaquetteHolonomy_replace_firstEdge
      n hn beta hBeta p A z2GaugeNontrivial
  change L.plaquetteHolonomy (L.replaceLink A e0 z2GaugeNontrivial) p =
    z2GaugeNontrivial * L.stepValue A (L.boundary p 1) *
      L.stepValue A (L.boundary p 2) *
      L.stepValue A (L.boundary p 3) at hHolonomyNontrivial
  have hObservableIdentity :
      z2PeriodicHypercubicPlaquetteEnergyObservable n beta hBeta p
          (L.replaceLink A e0 1) =
        if q = 1 then 0 else 1 := by
    unfold z2PeriodicHypercubicPlaquetteEnergyObservable
      FiniteOrientedLatticeWilsonSystem.plaquetteEnergyObservable
    rw [hHolonomyIdentity]
    change (if
        (1 : Z2Gauge) * L.stepValue A (L.boundary p 1) *
            L.stepValue A (L.boundary p 2) *
            L.stepValue A (L.boundary p 3) = 1
      then 0 else 1) = if q = 1 then 0 else 1
    simp [q]
  have hObservableNontrivial :
      z2PeriodicHypercubicPlaquetteEnergyObservable n beta hBeta p
          (L.replaceLink A e0 z2GaugeNontrivial) =
        if z2GaugeNontrivial * q = 1 then 0 else 1 := by
    unfold z2PeriodicHypercubicPlaquetteEnergyObservable
      FiniteOrientedLatticeWilsonSystem.plaquetteEnergyObservable
    rw [hHolonomyNontrivial]
    change (if
        z2GaugeNontrivial * L.stepValue A (L.boundary p 1) *
            L.stepValue A (L.boundary p 2) *
            L.stepValue A (L.boundary p 3) = 1
      then 0 else 1) =
        if z2GaugeNontrivial * q = 1 then 0 else 1
    simp [q, mul_assoc]
  rw [hObservableIdentity, hObservableNontrivial]
  exact z2Gauge_plaquetteEnergy_toggle_sq q

/-- The exact one-link conditional variance of the selected periodic `Z₂`
plaquette energy has the volume-independent lower bound `exp(-6β) / 8`. -/
theorem z2PeriodicHypercubicPlaquetteEnergyObservable_singleLinkConditionalVariance_lower
    (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (p : PeriodicHypercubicPlaquette n)
    (A : (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta).Configuration) :
    let L := z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta
    let e0 : L.Edge := (p.1, periodicHypercubicPlaquetteFirstAxis p)
    Real.exp (-(6 * beta)) / 8 ≤
      L.singleLinkConditionalVariance
        (z2PeriodicHypercubicPlaquetteEnergyObservable n beta hBeta p) A e0 := by
  let L := z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta
  let e0 : L.Edge := (p.1, periodicHypercubicPlaquetteFirstAxis p)
  let f := z2PeriodicHypercubicPlaquetteEnergyObservable n beta hBeta p
  change Real.exp (-(6 * beta)) / 8 ≤
    L.singleLinkConditionalVariance f A e0
  have hIdentity :=
    z2PeriodicHypercubic_singleLinkConditionalPMF_toReal_lower
      n beta hBeta A e0 (1 : Z2Gauge)
  have hNontrivial :=
    z2PeriodicHypercubic_singleLinkConditionalPMF_toReal_lower
      n beta hBeta A e0 z2GaugeNontrivial
  have hTwoPoint :=
    finite_oriented_singleLinkConditionalVariance_twoPoint_lower
      L f A e0 (1 : Z2Gauge) z2GaugeNontrivial
      (Real.exp (-(6 * beta)) / 2) hIdentity hNontrivial
  have hDifference :=
    z2PeriodicHypercubicPlaquetteEnergyObservable_replace_firstEdge_difference_sq
      n hn beta hBeta p A
  change (f (L.replaceLink A e0 1) -
      f (L.replaceLink A e0 z2GaugeNontrivial)) ^ 2 = 1 at hDifference
  calc
    Real.exp (-(6 * beta)) / 8 =
        (Real.exp (-(6 * beta)) / 2) * ((1 : ℝ) / 4) := by ring
    _ = (Real.exp (-(6 * beta)) / 2) *
        ((f (L.replaceLink A e0 1) -
          f (L.replaceLink A e0 z2GaugeNontrivial)) ^ 2 / 4) := by
      rw [hDifference]
    _ ≤ L.singleLinkConditionalVariance f A e0 := hTwoPoint

/-- The selected gauge-invariant periodic `Z₂` plaquette observable has the
explicit finite-volume Gibbs variance lower bound `exp(-6β) / 8`. -/
theorem z2PeriodicHypercubicPlaquetteEnergyObservable_gibbsVarianceReal_lower
    (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (p : PeriodicHypercubicPlaquette n) :
    let L := z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta
    Real.exp (-(6 * beta)) / 8 ≤
      L.gibbsVarianceReal
        (z2PeriodicHypercubicPlaquetteEnergyObservable n beta hBeta p) := by
  let L := z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta
  let e0 : L.Edge := (p.1, periodicHypercubicPlaquetteFirstAxis p)
  change Real.exp (-(6 * beta)) / 8 ≤
    L.gibbsVarianceReal
      (z2PeriodicHypercubicPlaquetteEnergyObservable n beta hBeta p)
  apply finite_oriented_lower_le_gibbsVarianceReal_of_conditional_pointwise
    L (z2PeriodicHypercubicPlaquetteEnergyObservable n beta hBeta p) e0
      (Real.exp (-(6 * beta)) / 8)
  intro A
  exact
    z2PeriodicHypercubicPlaquetteEnergyObservable_singleLinkConditionalVariance_lower
      n hn beta hBeta p A

end

end MathlibAnalytic
end MGAP4D
