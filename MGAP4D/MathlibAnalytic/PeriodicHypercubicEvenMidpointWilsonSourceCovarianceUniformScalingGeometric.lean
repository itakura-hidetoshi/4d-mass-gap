import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenMidpointWilsonSourceCovarianceScalingGeometric
import Mathlib.Tactic

/-!
# Uniform geometric envelope along a midpoint Wilson scaling sequence

The preceding scaling theorem leaves the finite Dobrushin coefficient

`rho_n = 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant (beta n)`

inside the eventual covariance estimate.  This file isolates the exact extra
input needed to replace that scale-dependent coefficient by one fixed geometric
ratio: an eventual bound `rho_n <= rhoBar` with `0 <= rhoBar < 1`.

For every fixed natural plaquette-local distance `D`, the actual finite midpoint
covariance then eventually satisfies

`|Cov_mid n| <= rhoBar^D / (1-rhoBar) * (8 * J.card * ‖F‖)^2`.

No claim is made here that the factorial continuum coupling supplies such a
`rhoBar`.  No weak-limit covariance transfer or Hamiltonian mass-gap conclusion
is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

local instance midpointWilsonSourceUniformScalingGeometricIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance midpointWilsonSourceUniformScalingGeometricCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

/-- On `[0,1)`, the finite geometric resolvent coefficient
`rho^D / (1-rho)` is monotone in `rho`. -/
theorem finite_geometric_resolvent_coefficient_le_of_le
    (rho rhoBar : ℝ)
    (D : ℕ)
    (hrho0 : 0 ≤ rho)
    (hrho_le : rho ≤ rhoBar)
    (hrhoBar1 : rhoBar < 1) :
    rho ^ D / (1 - rho) ≤ rhoBar ^ D / (1 - rhoBar) := by
  have hrhoBar0 : 0 ≤ rhoBar := hrho0.trans hrho_le
  have hrho1 : rho < 1 := hrho_le.trans_lt hrhoBar1
  have hpow : rho ^ D ≤ rhoBar ^ D :=
    pow_le_pow_left₀ hrho0 hrho_le D
  have hgap : 1 - rhoBar ≤ 1 - rho := by
    linarith
  have hgapBarPos : 0 < 1 - rhoBar := sub_pos.mpr hrhoBar1
  have hinv : (1 - rho)⁻¹ ≤ (1 - rhoBar)⁻¹ := by
    simpa only [one_div] using
      one_div_le_one_div_of_le hgapBarPos hgap
  rw [div_eq_mul_inv, div_eq_mul_inv]
  calc
    rho ^ D * (1 - rho)⁻¹ ≤ rhoBar ^ D * (1 - rho)⁻¹ :=
      mul_le_mul_of_nonneg_right hpow
        (inv_nonneg.mpr (sub_nonneg.mpr hrho1.le))
    _ ≤ rhoBar ^ D * (1 - rhoBar)⁻¹ :=
      mul_le_mul_of_nonneg_left hinv (pow_nonneg hrhoBar0 D)

/-- If the scale-dependent finite Dobrushin coefficient is eventually bounded
by one fixed `rhoBar < 1`, the scaling midpoint covariance estimate inherits a
fixed volume- and scale-independent geometric envelope. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointWilsonSourceCovariance_eventually_abs_le_uniformGeometric_of_scaling
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
    (rhoBar : ℝ)
    (hrhoBar0 : 0 ≤ rhoBar)
    (hrhoBar1 : rhoBar < 1)
    (hRhoLe :
      ∀ᶠ n : ℕ in atTop,
        18 * periodicHypercubicSpecialUnitaryActiveTVMajorant (beta n) ≤ rhoBar)
    (F : BoundedContinuousFunction (∀ q : J, ℝ) ℝ) :
    ∀ᶠ n : ℕ in atTop,
      |periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointWilsonSourceCovariance
          (H n) N hN (beta n) (hbeta n) latticeSpacing n J r F| ≤
        (rhoBar ^ D / (1 - rhoBar)) *
          (8 * (J.card : ℝ) * ‖F‖) ^ 2 := by
  have hThreshold :
      ∀ᶠ n : ℕ in atTop,
        18 * periodicHypercubicSpecialUnitaryActiveTVMajorant (beta n) < 1 :=
    hRhoLe.mono fun n hn => hn.trans_lt hrhoBar1
  have hScale :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointWilsonSourceCovariance_eventually_abs_le_geometric_uniformPrefactor_of_scaling
      H N D hN beta hbeta latticeSpacing latticeSpacing_pos
      latticeSpacing_tendsto_zero hreach J hJ r hr hThreshold F
  filter_upwards [hScale, hRhoLe] with n hCov hRho_n
  have hRhoNonneg :
      0 ≤ 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant (beta n) :=
    mul_nonneg (by norm_num)
      (periodicHypercubicSpecialUnitaryActiveTVMajorant_nonneg (beta n) (hbeta n))
  have hCoeff :=
    finite_geometric_resolvent_coefficient_le_of_le
      (18 * periodicHypercubicSpecialUnitaryActiveTVMajorant (beta n))
      rhoBar D hRhoNonneg hRho_n hrhoBar1
  calc
    |periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointWilsonSourceCovariance
        (H n) N hN (beta n) (hbeta n) latticeSpacing n J r F| ≤
      ((18 * periodicHypercubicSpecialUnitaryActiveTVMajorant (beta n)) ^ D /
        (1 - 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant (beta n))) *
        (8 * (J.card : ℝ) * ‖F‖) ^ 2 := hCov
    _ ≤
      (rhoBar ^ D / (1 - rhoBar)) *
        (8 * (J.card : ℝ) * ‖F‖) ^ 2 :=
      mul_le_mul_of_nonneg_right hCoeff (sq_nonneg _)

end

end MathlibAnalytic
end MGAP4D
