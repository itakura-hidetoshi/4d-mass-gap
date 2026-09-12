import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenMidpointWilsonSourceCovarianceUniformScalingGeometric
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Vanishing finite midpoint covariance along a scaling sequence

A uniform geometric ratio below one now gives, for every fixed plaquette-local
distance `D`, an eventual bound on the actual finite midpoint Wilson covariance.
The order of limits matters: first choose one fixed `D` making the uniform
geometric envelope arbitrarily small, then use the eventual-in-scale estimate
for that `D`.

This proves that the actual finite-volume midpoint covariance sequence tends to
zero under the explicit uniform Dobrushin-ratio hypothesis.  It is still a
statement about finite Wilson Gibbs measures along the scaling sequence.  No
weak-limit covariance identification, continuum clustering theorem, or
Hamiltonian mass gap is asserted here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

local instance midpointWilsonSourceScalingLimitZeroIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance midpointWilsonSourceScalingLimitZeroCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

/-- If every fixed geometric distance eventually bounds a real sequence by
`C * q^D`, with `0 <= q < 1`, then the sequence tends to zero.  The distance
`D` is selected from the target neighborhood before the eventual scale bound is
used. -/
theorem tendsto_zero_of_forall_eventually_abs_le_geometric
    (f : ℕ → ℝ)
    (C q : ℝ)
    (hq0 : 0 ≤ q)
    (hq1 : q < 1)
    (hbound : ∀ D : ℕ, ∀ᶠ n : ℕ in atTop, |f n| ≤ C * q ^ D) :
    Tendsto f atTop (nhds 0) := by
  have hq : Tendsto (fun D : ℕ => q ^ D) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have hEnvelope :
      Tendsto (fun D : ℕ => C * q ^ D) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hq)
  have hAbs : Tendsto (fun n : ℕ => |f n|) atTop (nhds 0) := by
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro a ha
      exact Filter.Eventually.of_forall fun n =>
        lt_of_lt_of_le ha (abs_nonneg (f n))
    · intro b hb
      have hSmall : ∀ᶠ D : ℕ in atTop, C * q ^ D < b :=
        (tendsto_order.1 hEnvelope).2 b hb
      obtain ⟨D, hD⟩ := eventually_atTop.1 hSmall
      exact (hbound D).mono fun n hn =>
        lt_of_le_of_lt hn (hD D le_rfl)
  apply tendsto_zero_iff_norm_tendsto_zero.2
  simpa [Real.norm_eq_abs] using hAbs

/-- Under the same scaling assumptions as the uniform geometric theorem, if the
scale-dependent finite Dobrushin coefficients are eventually dominated by one
fixed `rhoBar < 1`, then the actual finite midpoint Wilson covariance tends to
zero as the lattice scale tends to infinity. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointWilsonSourceCovariance_tendsto_zero_of_uniformGeometric_scaling
    (H : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero : Tendsto latticeSpacing atTop (nhds 0))
    (hreach :
      Tendsto
        (periodicHypercubicEvenPrimarySpatialPhysicalTemporalReach H latticeSpacing)
        atTop atTop)
    (J : Finset ℚ)
    (hJ : ∀ q : ℚ, q ∈ J → 0 ≤ q)
    (r : ℚ)
    (hr : 0 < r)
    (rhoBar : ℝ)
    (hrhoBar0 : 0 ≤ rhoBar)
    (hrhoBar1 : rhoBar < 1)
    (hRhoLe :
      ∀ᶠ n : ℕ in atTop,
        18 * periodicHypercubicSpecialUnitaryActiveTVMajorant (beta n) ≤ rhoBar)
    (F : BoundedContinuousFunction (∀ q : J, ℝ) ℝ) :
    Tendsto
      (fun n : ℕ =>
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointWilsonSourceCovariance
          (H n) N hN (beta n) (hbeta n) latticeSpacing n J r F)
      atTop (nhds 0) := by
  let K : ℝ := 8 * (J.card : ℝ) * ‖F‖
  let C : ℝ := (1 - rhoBar)⁻¹ * K ^ 2
  apply
    tendsto_zero_of_forall_eventually_abs_le_geometric
      (fun n : ℕ =>
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointWilsonSourceCovariance
          (H n) N hN (beta n) (hbeta n) latticeSpacing n J r F)
      C rhoBar hrhoBar0 hrhoBar1
  intro D
  have hD :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointWilsonSourceCovariance_eventually_abs_le_uniformGeometric_of_scaling
      H N D hN beta hbeta latticeSpacing latticeSpacing_pos
      latticeSpacing_tendsto_zero hreach J hJ r hr rhoBar
      hrhoBar0 hrhoBar1 hRhoLe F
  filter_upwards [hD] with n hn
  calc
    |periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointWilsonSourceCovariance
        (H n) N hN (beta n) (hbeta n) latticeSpacing n J r F| ≤
      (rhoBar ^ D / (1 - rhoBar)) * K ^ 2 := by
        simpa [K] using hn
    _ = C * rhoBar ^ D := by
      dsimp [C]
      rw [div_eq_mul_inv]
      ring

end

end MathlibAnalytic
end MGAP4D
