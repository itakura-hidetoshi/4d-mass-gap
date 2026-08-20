import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitRegularYosidaTimeAverageDuhamelConvergence
import Mathlib.Tactic

/-!
# Strong Yosida exponential convergence on the full regular OS Hilbert sector

The preceding same-root Duhamel layer proves locally uniform convergence of the bounded dyadic
Yosida exponentials to the original regular OS semigroup on every positive-time Cesàro average.
Those averages converge strongly back to every regular vector.  Since both the Yosida exponential
semigroups and the original OS semigroup are contractions, the standard three-term density estimate
extends the compact-time convergence to the whole complete regular Hilbert sector.

Thus the original same-root OS `C₀` semigroup is identified pointwise, and locally uniformly on every
compact nonnegative-time interval, as the strong limit of the bounded Yosida exponentials
`exp (-t H_{2^n})`.

No spectral functional calculus, no abstract Trotter--Kato theorem, and no new analytic hypothesis is
introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter Set Topology
open scoped InnerProductSpace LinearPMap

noncomputable section

namespace PrimaryScalarFixedSlotOSPreHilbertData

variable {H : ℕ → ℕ}
variable {N : ℕ} {hN : 0 < N}
variable [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
variable {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable {L :
  PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
    H N hN beta hbeta
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing}

/-- Every regular vector can be approximated arbitrarily well by a strictly positive-time Cesàro
average from the canonical generator core. -/
theorem fixedSlotHilbertDirectLimitRegularTimeAverage_exists_norm_sub_lt
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ h : NNReal, 0 < h ∧
      ‖P.fixedSlotHilbertDirectLimitRegularTimeAverage h x - x‖ < δ := by
  have hlim := P.fixedSlotHilbertDirectLimitRegularTimeAverage_tendsto_zero x
  have hnear : ∀ᶠ h : NNReal in nhdsWithin 0 (Ioi 0),
      P.fixedSlotHilbertDirectLimitRegularTimeAverage h x ∈ Metric.ball x δ :=
    hlim (Metric.ball_mem_nhds x hδ)
  have hpos : ∀ᶠ h : NNReal in nhdsWithin 0 (Ioi 0), h ∈ Ioi 0 :=
    self_mem_nhdsWithin
  rcases (hnear.and hpos).exists with ⟨h, hhball, hhpos⟩
  refine ⟨h, hhpos, ?_⟩
  simpa only [Metric.mem_ball, dist_eq_norm] using hhball

/-- Locally uniform Yosida exponential convergence on compact nonnegative-time intervals for every
vector of the complete regular OS Hilbert sector. -/
theorem fixedSlotHilbertDirectLimitRegularYosidaExponential_tendsto_uniformOn_compact
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (R : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ t : NNReal, t ≤ R →
      ‖P.fixedSlotHilbertDirectLimitRegularDyadicYosidaExponential n t x -
          P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t x‖ < ε := by
  have hε4 : 0 < ε / 4 := by linarith
  have hε2 : 0 < ε / 2 := by linarith
  rcases P.fixedSlotHilbertDirectLimitRegularTimeAverage_exists_norm_sub_lt x hε4 with
    ⟨h, _hhpos, hh⟩
  let z : P.fixedSlotHilbertDirectLimitRegularSubspace :=
    P.fixedSlotHilbertDirectLimitRegularTimeAverage h x
  have hzx : ‖z - x‖ < ε / 4 := by
    simpa only [z] using hh
  have hxz : ‖x - z‖ < ε / 4 := by
    simpa only [norm_sub_rev] using hzx
  have hcore :=
    P.fixedSlotHilbertDirectLimitRegularTimeAverageYosidaExponential_tendsto_uniformOn_compact
      R h x hε2
  filter_upwards [hcore] with n hn
  intro t ht
  have hE :
      ‖P.fixedSlotHilbertDirectLimitRegularDyadicYosidaExponential n t (x - z)‖ ≤
        ‖x - z‖ :=
    P.fixedSlotHilbertDirectLimitRegularDyadicYosidaExponential_norm_le n t (x - z)
  have hT :
      ‖P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t (z - x)‖ ≤
        ‖z - x‖ :=
    P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_norm_le t (z - x)
  have hmid :
      ‖P.fixedSlotHilbertDirectLimitRegularDyadicYosidaExponential n t z -
          P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t z‖ < ε / 2 := by
    simpa only [z] using hn t ht
  have hdecomp :
      P.fixedSlotHilbertDirectLimitRegularDyadicYosidaExponential n t x -
          P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t x =
        P.fixedSlotHilbertDirectLimitRegularDyadicYosidaExponential n t (x - z) +
          (P.fixedSlotHilbertDirectLimitRegularDyadicYosidaExponential n t z -
            P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t z) +
          P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t (z - x) := by
    rw [map_sub, map_sub]
    module
  rw [hdecomp]
  calc
    ‖P.fixedSlotHilbertDirectLimitRegularDyadicYosidaExponential n t (x - z) +
        (P.fixedSlotHilbertDirectLimitRegularDyadicYosidaExponential n t z -
          P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t z) +
        P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t (z - x)‖ ≤
      ‖P.fixedSlotHilbertDirectLimitRegularDyadicYosidaExponential n t (x - z) +
        (P.fixedSlotHilbertDirectLimitRegularDyadicYosidaExponential n t z -
          P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t z)‖ +
        ‖P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t (z - x)‖ :=
      norm_add_le _ _
    _ ≤
      (‖P.fixedSlotHilbertDirectLimitRegularDyadicYosidaExponential n t (x - z)‖ +
        ‖P.fixedSlotHilbertDirectLimitRegularDyadicYosidaExponential n t z -
          P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t z‖) +
        ‖P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t (z - x)‖ := by
      exact add_le_add (norm_add_le _ _) (le_refl _)
    _ < ε := by linarith

/-- For every fixed nonnegative time, the bounded dyadic Yosida exponential converges strongly to
the original same-root regular OS semigroup. -/
theorem fixedSlotHilbertDirectLimitRegularDyadicYosidaExponential_tendsto_originalSemigroup
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    Tendsto
      (fun n : ℕ => P.fixedSlotHilbertDirectLimitRegularDyadicYosidaExponential n t x)
      atTop
      (nhds (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have huni :=
    P.fixedSlotHilbertDirectLimitRegularYosidaExponential_tendsto_uniformOn_compact t x hε
  rcases eventually_atTop.1 huni with ⟨N0, hN0⟩
  refine ⟨N0, ?_⟩
  intro n hn
  have hpoint := hN0 n hn t (le_refl t)
  simpa only [dist_eq_norm] using hpoint

/-- Full same-root Yosida semigroup convergence and identification package.  The first component is
compact-time locally uniform strong convergence for every regular vector; the second records the
pointwise strong identification of the original OS semigroup with the Yosida exponential limit. -/
theorem fixedSlotHilbertDirectLimitRegularYosidaExponentialConvergence_package
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    (∀ R : NNReal, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, ∀ t : NNReal, t ≤ R →
        ‖P.fixedSlotHilbertDirectLimitRegularDyadicYosidaExponential n t x -
            P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t x‖ < ε) ∧
    (∀ t : NNReal,
      Tendsto
        (fun n : ℕ => P.fixedSlotHilbertDirectLimitRegularDyadicYosidaExponential n t x)
        atTop
        (nhds (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t x))) := by
  refine ⟨?_, ?_⟩
  · intro R ε hε
    exact P.fixedSlotHilbertDirectLimitRegularYosidaExponential_tendsto_uniformOn_compact R x hε
  · intro t
    exact P.fixedSlotHilbertDirectLimitRegularDyadicYosidaExponential_tendsto_originalSemigroup t x

end PrimaryScalarFixedSlotOSPreHilbertData

end
end MathlibAnalytic
end MGAP4D
