import MGAP4D.MathlibAnalytic.FiniteOrientedWilsonPlaquetteEnergyObservable
import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicOrientedWilsonSystem
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A nontrivial periodic shift cannot fix a vertex when the side length is at
least two. -/
theorem periodicHypercubicShift_ne_self_of_two_le
    (n : ℕ) [NeZero n]
    (hn : 2 ≤ n)
    (x : PeriodicHypercubicVertex n)
    (mu : PeriodicHypercubicAxis) :
    periodicHypercubicShift n x mu ≠ x := by
  intro h
  have hcoord : x mu + 1 = x mu := by
    simpa [periodicHypercubicShift_apply] using congrFun h mu
  have hOne : (1 : ZMod n) = 0 := by
    apply add_left_cancel (a := x mu)
    simpa using hcoord
  have hval := congrArg ZMod.val hOne
  have hvalOne : ZMod.val (1 : ZMod n) = 1 := by
    change ((1 : ℕ) : ZMod n).val = 1
    exact ZMod.val_natCast_of_lt (by omega)
  have hvalZero : ZMod.val (0 : ZMod n) = 0 := rfl
  rw [hvalOne, hvalZero] at hval
  omega

/-- The energy of one selected plaquette in the periodic oriented `Z₂` Wilson
system. -/
def z2PeriodicHypercubicPlaquetteEnergyObservable
    (n : ℕ) [NeZero n]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (p : PeriodicHypercubicPlaquette n) :
    (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta).Configuration → ℝ :=
  FiniteOrientedLatticeWilsonSystem.plaquetteEnergyObservable
    (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta) p

/-- The concrete selected `Z₂` plaquette energy is gauge invariant. -/
theorem z2PeriodicHypercubicPlaquetteEnergyObservable_gaugeInvariant
    (n : ℕ) [NeZero n]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (p : PeriodicHypercubicPlaquette n)
    (gamma :
      (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta).GaugeTransformation)
    (A :
      (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta).Configuration) :
    z2PeriodicHypercubicPlaquetteEnergyObservable n beta hBeta p
        ((z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
          .gaugeTransform gamma A) =
      z2PeriodicHypercubicPlaquetteEnergyObservable n beta hBeta p A :=
  finite_oriented_plaquetteEnergyObservable_gaugeInvariant
    (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta) p gamma A

/-- For side length at least two, one selected periodic `Z₂` plaquette energy
attains both `0` and `1` on two explicit physical-link configurations. -/
theorem z2PeriodicHypercubicPlaquetteEnergyObservable_has_two_values
    (n : ℕ) [NeZero n]
    (hn : 2 ≤ n)
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (p : PeriodicHypercubicPlaquette n) :
    let L := z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta
    let A₀ : L.Configuration := fun _ => 1
    let e₀ : L.Edge :=
      (p.1, periodicHypercubicPlaquetteFirstAxis p)
    let A₁ : L.Configuration :=
      L.replaceLink A₀ e₀ z2GaugeNontrivial
    z2PeriodicHypercubicPlaquetteEnergyObservable n beta hBeta p A₀ = 0 ∧
      z2PeriodicHypercubicPlaquetteEnergyObservable n beta hBeta p A₁ = 1 := by
  let L := z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta
  let mu := periodicHypercubicPlaquetteFirstAxis p
  let nu := periodicHypercubicPlaquetteSecondAxis p
  let e₀ : L.Edge := (p.1, mu)
  let A₀ : L.Configuration := fun _ => 1
  let A₁ : L.Configuration :=
    L.replaceLink A₀ e₀ z2GaugeNontrivial
  have hmuNu : mu ≠ nu := by
    exact periodicHypercubicPlaquette_axes_ne p
  have he₁ : (periodicHypercubicShift n p.1 mu, nu) ≠ e₀ := by
    intro h
    have hsnd := congrArg Prod.snd h
    exact hmuNu hsnd.symm
  have he₂ : (periodicHypercubicShift n p.1 nu, mu) ≠ e₀ := by
    intro h
    have hfst := congrArg Prod.fst h
    exact periodicHypercubicShift_ne_self_of_two_le n hn p.1 nu hfst
  have he₃ : (p.1, nu) ≠ e₀ := by
    intro h
    have hsnd := congrArg Prod.snd h
    exact hmuNu hsnd.symm
  have hA₀Step : ∀ s : FiniteOrientedBoundaryStep L.Edge,
      L.stepValue A₀ s = 1 := by
    intro s
    cases s with
    | mk edge orientation =>
        cases orientation <;>
          simp [FiniteOrientedLatticeWilsonSystem.stepValue, A₀]
  have hHolonomy₀ : L.plaquetteHolonomy A₀ p = 1 := by
    unfold FiniteOrientedLatticeWilsonSystem.plaquetteHolonomy
    rw [hA₀Step, hA₀Step, hA₀Step, hA₀Step]
    simp
  have hStep₀ : L.stepValue A₁ (L.boundary p 0) = z2GaugeNontrivial := by
    change L.replaceLink A₀ e₀ z2GaugeNontrivial e₀ = z2GaugeNontrivial
    rw [finite_oriented_replaceLink_same]
  have hStep₁ : L.stepValue A₁ (L.boundary p 1) = 1 := by
    change L.replaceLink A₀ e₀ z2GaugeNontrivial
      (periodicHypercubicShift n p.1 mu, nu) = 1
    rw [finite_oriented_replaceLink_of_ne L A₀ e₀
      (periodicHypercubicShift n p.1 mu, nu) z2GaugeNontrivial he₁]
    rfl
  have hStep₂ : L.stepValue A₁ (L.boundary p 2) = 1 := by
    change (L.replaceLink A₀ e₀ z2GaugeNontrivial
      (periodicHypercubicShift n p.1 nu, mu))⁻¹ = 1
    rw [finite_oriented_replaceLink_of_ne L A₀ e₀
      (periodicHypercubicShift n p.1 nu, mu) z2GaugeNontrivial he₂]
    simp
  have hStep₃ : L.stepValue A₁ (L.boundary p 3) = 1 := by
    change (L.replaceLink A₀ e₀ z2GaugeNontrivial (p.1, nu))⁻¹ = 1
    rw [finite_oriented_replaceLink_of_ne L A₀ e₀
      (p.1, nu) z2GaugeNontrivial he₃]
    simp
  have hHolonomy₁ : L.plaquetteHolonomy A₁ p = z2GaugeNontrivial := by
    unfold FiniteOrientedLatticeWilsonSystem.plaquetteHolonomy
    rw [hStep₀, hStep₁, hStep₂, hStep₃]
    simp
  constructor
  · unfold z2PeriodicHypercubicPlaquetteEnergyObservable
      FiniteOrientedLatticeWilsonSystem.plaquetteEnergyObservable
    rw [hHolonomy₀]
    rfl
  · unfold z2PeriodicHypercubicPlaquetteEnergyObservable
      FiniteOrientedLatticeWilsonSystem.plaquetteEnergyObservable
    rw [hHolonomy₁]
    simp [L, z2PeriodicHypercubicOrientedWilsonSystem, z2GaugeNontrivial]

/-- Every finite periodic oriented `Z₂` Wilson Gibbs law of side length at least
`2` has strictly positive variance for a concrete gauge-invariant plaquette
energy observable.  This remains a finite-volume statement. -/
theorem z2PeriodicHypercubicPlaquetteEnergyObservable_gibbsVarianceReal_pos
    (n : ℕ) [NeZero n]
    (hn : 2 ≤ n)
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (p : PeriodicHypercubicPlaquette n) :
    let L := z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta
    0 < L.gibbsVarianceReal
      (z2PeriodicHypercubicPlaquetteEnergyObservable n beta hBeta p) := by
  let L := z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta
  let A₀ : L.Configuration := fun _ => 1
  let e₀ : L.Edge :=
    (p.1, periodicHypercubicPlaquetteFirstAxis p)
  let A₁ : L.Configuration :=
    L.replaceLink A₀ e₀ z2GaugeNontrivial
  change 0 < L.gibbsVarianceReal (L.plaquetteEnergyObservable p)
  apply finite_oriented_plaquetteEnergyObservable_gibbsVarianceReal_pos_of_exists_ne
    L p A₀ A₁
  change z2PeriodicHypercubicPlaquetteEnergyObservable n beta hBeta p A₀ ≠
    z2PeriodicHypercubicPlaquetteEnergyObservable n beta hBeta p A₁
  have hValues :=
    z2PeriodicHypercubicPlaquetteEnergyObservable_has_two_values
      n hn beta hBeta p
  dsimp [L, A₀, e₀, A₁] at hValues ⊢
  rw [hValues.1, hValues.2]
  norm_num

end

end MathlibAnalytic
end MGAP4D
