import MGAP4D.MathlibAnalytic.FiniteOrientedWilsonFullSupportVarianceDefiniteness
import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicOrientedWilsonSystem
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Real spin coordinate on the two-element multiplicative gauge group. -/
def z2GaugeSpin (g : Z2Gauge) : ℝ :=
  if g = 1 then 1 else -1

@[simp] theorem z2GaugeSpin_one :
    z2GaugeSpin (1 : Z2Gauge) = 1 := by
  simp [z2GaugeSpin]

@[simp] theorem z2GaugeSpin_nontrivial :
    z2GaugeSpin z2GaugeNontrivial = -1 := by
  simp [z2GaugeSpin, z2GaugeNontrivial]

/-- The spin observed on one physical positive link of the periodic oriented
`Z₂` Wilson system. -/
def z2PeriodicHypercubicLinkSpinObservable
    (n : ℕ) [NeZero n]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (target : PeriodicHypercubicEdge n) :
    (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta).Configuration → ℝ :=
  fun A => z2GaugeSpin (A target)

/-- Replacing the selected physical link by the nonidentity `Z₂` element changes
its real spin observable from `1` to `-1`. -/
theorem z2PeriodicHypercubicLinkSpinObservable_has_two_values
    (n : ℕ) [NeZero n]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (target : PeriodicHypercubicEdge n) :
    let L := z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta
    let A₀ : L.Configuration := fun _ => 1
    z2PeriodicHypercubicLinkSpinObservable n beta hBeta target A₀ = 1 ∧
      z2PeriodicHypercubicLinkSpinObservable n beta hBeta target
          (L.replaceLink A₀ target z2GaugeNontrivial) = -1 := by
  constructor
  · simp [z2PeriodicHypercubicLinkSpinObservable]
  · simp [z2PeriodicHypercubicLinkSpinObservable]

/-- Every finite periodic oriented `Z₂` Wilson Gibbs law has a genuinely
fluctuating single-link spin observable.  This is a finite-volume positivity
statement; no scale-uniform lower bound is asserted here. -/
theorem z2PeriodicHypercubicLinkSpinObservable_gibbsVarianceReal_pos
    (n : ℕ) [NeZero n]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (target : PeriodicHypercubicEdge n) :
    let L := z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta
    0 < L.gibbsVarianceReal
      (z2PeriodicHypercubicLinkSpinObservable n beta hBeta target) := by
  let L := z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta
  let A₀ : L.Configuration := fun _ => 1
  let A₁ : L.Configuration :=
    L.replaceLink A₀ target z2GaugeNontrivial
  apply finite_oriented_gibbsVarianceReal_pos_of_exists_ne L
    (z2PeriodicHypercubicLinkSpinObservable n beta hBeta target) A₀ A₁
  have hValues :=
    z2PeriodicHypercubicLinkSpinObservable_has_two_values
      n beta hBeta target
  dsimp [L, A₀, A₁] at hValues ⊢
  rw [hValues.1, hValues.2]
  norm_num

end

end MathlibAnalytic
end MGAP4D
