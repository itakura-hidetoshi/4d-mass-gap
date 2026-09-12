import MGAP4D.MathlibAnalytic.FiniteOrientedWilsonPlaquetteEnergyObservable
import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicOrientedWilsonSystem
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

theorem periodicHypercubicShift_ne_self_of_two_le
    (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (x : PeriodicHypercubicVertex n) (mu : PeriodicHypercubicAxis) :
    periodicHypercubicShift n x mu ≠ x := by
  intro h
  have hcoord : x mu + 1 = x mu := by
    simpa [periodicHypercubicShift_apply] using congrFun h mu
  have hOne : (1 : ZMod n) = 0 := by
    apply add_left_cancel (a := x mu)
    simpa using hcoord
  letI : Fact (1 < n) := ⟨by omega⟩
  exact one_ne_zero hOne

def z2PeriodicHypercubicPlaquetteEnergyObservable
    (n : ℕ) [NeZero n] (beta : ℝ) (hBeta : 0 ≤ beta)
    (p : PeriodicHypercubicPlaquette n) :
    (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta).Configuration → ℝ :=
  FiniteOrientedLatticeWilsonSystem.plaquetteEnergyObservable
    (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta) p

theorem z2PeriodicHypercubicPlaquetteEnergyObservable_gaugeInvariant
    (n : ℕ) [NeZero n] (beta : ℝ) (hBeta : 0 ≤ beta)
    (p : PeriodicHypercubicPlaquette n)
    (gamma : (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta).GaugeTransformation)
    (A : (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta).Configuration) :
    z2PeriodicHypercubicPlaquetteEnergyObservable n beta hBeta p
        (FiniteOrientedLatticeWilsonSystem.gaugeTransform
          (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta) gamma A) =
      z2PeriodicHypercubicPlaquetteEnergyObservable n beta hBeta p A :=
  finite_oriented_plaquetteEnergyObservable_gaugeInvariant
    (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta) p gamma A

theorem z2PeriodicHypercubicPlaquetteEnergyObservable_has_two_values
    (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (p : PeriodicHypercubicPlaquette n) :
    let L := z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta
    let A0 : L.Configuration := fun _ => 1
    let e0 : L.Edge := (p.1, periodicHypercubicPlaquetteFirstAxis p)
    let A1 : L.Configuration := L.replaceLink A0 e0 z2GaugeNontrivial
    z2PeriodicHypercubicPlaquetteEnergyObservable n beta hBeta p A0 = 0 ∧
      z2PeriodicHypercubicPlaquetteEnergyObservable n beta hBeta p A1 = 1 := by
  let L := z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta
  let mu := periodicHypercubicPlaquetteFirstAxis p
  let nu := periodicHypercubicPlaquetteSecondAxis p
  let e0 : L.Edge := (p.1, mu)
  let A0 : L.Configuration := fun _ => 1
  let A1 : L.Configuration := L.replaceLink A0 e0 z2GaugeNontrivial
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
  have hA0Step : ∀ s : FiniteOrientedBoundaryStep L.Edge,
      L.stepValue A0 s = 1 := by
    intro s
    cases s with
    | mk edge orientation =>
        cases orientation <;>
          simp [FiniteOrientedLatticeWilsonSystem.stepValue, A0]
  have hHolonomy0 : L.plaquetteHolonomy A0 p = 1 := by
    unfold FiniteOrientedLatticeWilsonSystem.plaquetteHolonomy
    rw [hA0Step, hA0Step, hA0Step, hA0Step]
    simp
  have hStep0 : L.stepValue A1 (L.boundary p 0) = z2GaugeNontrivial := by
    change L.replaceLink A0 e0 z2GaugeNontrivial e0 = z2GaugeNontrivial
    rw [finite_oriented_replaceLink_same]
  have hStep1 : L.stepValue A1 (L.boundary p 1) = 1 := by
    change L.replaceLink A0 e0 z2GaugeNontrivial
      (periodicHypercubicShift n p.1 mu, nu) = 1
    simpa [A0] using
      finite_oriented_replaceLink_of_ne L A0 e0
        (periodicHypercubicShift n p.1 mu, nu) z2GaugeNontrivial he1
  have hStep2 : L.stepValue A1 (L.boundary p 2) = 1 := by
    change (L.replaceLink A0 e0 z2GaugeNontrivial
      (periodicHypercubicShift n p.1 nu, mu))⁻¹ = 1
    have hReplace := finite_oriented_replaceLink_of_ne L A0 e0
      (periodicHypercubicShift n p.1 nu, mu) z2GaugeNontrivial he2
    simpa [A0] using congrArg Inv.inv hReplace
  have hStep3 : L.stepValue A1 (L.boundary p 3) = 1 := by
    change (L.replaceLink A0 e0 z2GaugeNontrivial (p.1, nu))⁻¹ = 1
    have hReplace := finite_oriented_replaceLink_of_ne L A0 e0
      (p.1, nu) z2GaugeNontrivial he3
    simpa [A0] using congrArg Inv.inv hReplace
  have hHolonomy1 : L.plaquetteHolonomy A1 p = z2GaugeNontrivial := by
    unfold FiniteOrientedLatticeWilsonSystem.plaquetteHolonomy
    rw [hStep0, hStep1, hStep2, hStep3]
    simp
  constructor
  · unfold z2PeriodicHypercubicPlaquetteEnergyObservable
      FiniteOrientedLatticeWilsonSystem.plaquetteEnergyObservable
    rw [hHolonomy0]
    rfl
  · unfold z2PeriodicHypercubicPlaquetteEnergyObservable
      FiniteOrientedLatticeWilsonSystem.plaquetteEnergyObservable
    rw [hHolonomy1]
    simp [z2PeriodicHypercubicOrientedWilsonSystem, z2GaugeNontrivial]

theorem z2PeriodicHypercubicPlaquetteEnergyObservable_gibbsVarianceReal_pos
    (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (p : PeriodicHypercubicPlaquette n) :
    let L := z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta
    0 < L.gibbsVarianceReal
      (z2PeriodicHypercubicPlaquetteEnergyObservable n beta hBeta p) := by
  let L := z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta
  let A0 : L.Configuration := fun _ => 1
  let e0 : L.Edge := (p.1, periodicHypercubicPlaquetteFirstAxis p)
  let A1 : L.Configuration := L.replaceLink A0 e0 z2GaugeNontrivial
  change 0 < L.gibbsVarianceReal (L.plaquetteEnergyObservable p)
  apply finite_oriented_plaquetteEnergyObservable_gibbsVarianceReal_pos_of_exists_ne
    L p A0 A1
  change z2PeriodicHypercubicPlaquetteEnergyObservable n beta hBeta p A0 ≠
    z2PeriodicHypercubicPlaquetteEnergyObservable n beta hBeta p A1
  have hValues := z2PeriodicHypercubicPlaquetteEnergyObservable_has_two_values
    n hn beta hBeta p
  dsimp [L, A0, e0, A1] at hValues ⊢
  rw [hValues.1, hValues.2]
  norm_num

end

end MathlibAnalytic
end MGAP4D
