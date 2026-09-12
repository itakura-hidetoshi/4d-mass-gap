import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenMidpointWilsonSourceCovarianceUniformPrefactor
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenMidpointWilsonSourceScalingSeparation
import Mathlib.Tactic

/-!
# Scaling lift of finite midpoint Wilson covariance decay

The finite midpoint Wilson-source covariance now has a volume-independent
observable prefactor, while the scaling geometry already proves that every
fixed plaquette-local distance `D` is eventually realized by the literal
reflected-left and translated-right supports.

This file joins those two canonical layers for a scale-dependent Wilson
coupling `beta n`.  If the explicit finite-scale Dobrushin threshold holds
eventually along the sequence, then for every fixed natural distance `D` the
actual finite midpoint covariance eventually satisfies

`|Cov_mid n| <= rho_n^D / (1-rho_n) * (8 * J.card * ‖F‖)^2`,

where `rho_n = 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant (beta n)`.

This is deliberately an eventual finite-scale estimate.  It does not assert
that the factorial continuum coupling satisfies the Dobrushin threshold, does
not yet replace `rho_n` by a uniform number below one, does not pass covariance
to a weak limit, and does not assert a Hamiltonian mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

local instance midpointWilsonSourceScalingGeometricIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance midpointWilsonSourceScalingGeometricCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

/-- Under vanishing lattice spacing, divergent primary temporal reach, a
strictly positive midpoint offset, and an eventual finite-scale Dobrushin
threshold, every fixed natural separation `D` eventually gives the canonical
volume-independent geometric midpoint covariance estimate. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointWilsonSourceCovariance_eventually_abs_le_geometric_uniformPrefactor_of_scaling
    (H : ℕ → ℕ)
    (N D : ℕ)
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
    (hThreshold :
      ∀ᶠ n : ℕ in atTop,
        18 * periodicHypercubicSpecialUnitaryActiveTVMajorant (beta n) < 1)
    (F : BoundedContinuousFunction (∀ q : J, ℝ) ℝ) :
    ∀ᶠ n : ℕ in atTop,
      |periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointWilsonSourceCovariance
          (H n) N hN (beta n) (hbeta n) latticeSpacing n J r F| ≤
        ((18 * periodicHypercubicSpecialUnitaryActiveTVMajorant (beta n)) ^ D /
          (1 - 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant (beta n))) *
          (8 * (J.card : ℝ) * ‖F‖) ^ 2 := by
  have hReachOne :
      ∀ᶠ n : ℕ in atTop,
        (1 : ℝ) ≤
          periodicHypercubicEvenPrimarySpatialPhysicalTemporalReach
            H latticeSpacing n :=
    tendsto_atTop.1 hreach 1
  have hHPos : ∀ᶠ n : ℕ in atTop, 0 < H n := by
    filter_upwards [hReachOne] with n hn
    by_contra hNotPos
    have hHzero : H n = 0 := Nat.eq_zero_of_not_pos hNotPos
    have hImpossible : (1 : ℝ) ≤ 0 := by
      simpa [periodicHypercubicEvenPrimarySpatialPhysicalTemporalReach, hHzero] using hn
    norm_num at hImpossible
  have hSum :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpoint_eventually_floor_sum_ge_of_spacing_tendsto_zero
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      J hJ r hr D
  have hMargins :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpoint_eventually_interior_margins_of_scaling
      H latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero hreach
      J hJ r hr.le D
  filter_upwards [hThreshold, hHPos, hSum, hMargins] with
      n hThreshold_n hH_n hSum_n hMargins_n
  have hWithin :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpoint_within_of_interior_margin
      (H n) latticeSpacing n J r D hMargins_n.1 hMargins_n.2
  have hFloor :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpoint_floor_min_ge_of_sum_ge_of_interior_margin
      (H n) latticeSpacing n J r D hSum_n hMargins_n.1 hMargins_n.2
  exact
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointWilsonSourceCovariance_abs_le_geometric_uniformPrefactor_of_floor_min_ge
      (H n) N D hH_n hN (beta n) (hbeta n) hThreshold_n
      latticeSpacing n J hJ r hr.le hWithin.1 hWithin.2 hFloor F

end

end MathlibAnalytic
end MGAP4D
