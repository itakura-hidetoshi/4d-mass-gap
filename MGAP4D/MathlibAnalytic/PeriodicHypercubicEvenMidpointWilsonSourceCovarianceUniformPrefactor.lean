import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenMidpointWilsonSourceCovarianceGeometric
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenMidpointWilsonSupportCardinality
import Mathlib.Tactic

/-!
# Volume-independent prefactor for finite midpoint Wilson covariance decay

The geometric midpoint covariance theorem still displays two finite support
sums.  The source BCFs are pullbacks of the original fixed-slot observable and
therefore have no larger sup norm, while the two midpoint supports contain at
most four physical links per rational slot.  Hence each support sum is bounded
by

`8 * J.card * ‖F‖`.

Combining these estimates with the finite-scale geometric covariance theorem
gives a prefactor depending only on the finite slot count and the original
observable norm, not on finite lattice volume, lattice spacing, or midpoint
translation:

`|Cov_mid| ≤ rho^D / (1-rho) * (8 * J.card * ‖F‖)^2`.

The strict Dobrushin threshold remains an explicit finite-scale hypothesis.
This file does not prove that threshold uniformly along a continuum sequence,
does not take a continuum limit, and does not assert a Hamiltonian mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

private instance midpointWilsonSourceUniformPrefactorSideLengthNeZero
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) :=
  ⟨by simp [PeriodicHypercubicEvenSideLength]⟩

local instance midpointWilsonSourceUniformPrefactorIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance midpointWilsonSourceUniformPrefactorCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

/-- The translated-right support sum appearing in the finite clustering theorem
is bounded solely by the slot count and the original fixed-slot observable
norm. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightSupport_sum_two_mul_sourceNorm_le
    (H N : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (hJ : ∀ q : ℚ, q ∈ J → 0 ≤ q)
    (r : ℚ)
    (hr : 0 ≤ r)
    (F : BoundedContinuousFunction (∀ q : J, ℝ) ℝ) :
    (∑ e ∈
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightSupport
          H latticeSpacing n J r,
      2 * ‖periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightWilsonSourceBCF
        H N latticeSpacing n J hJ r hr F‖) ≤
      8 * (J.card : ℝ) * ‖F‖ := by
  let Right :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightWilsonSourceBCF
      H N latticeSpacing n J hJ r hr F
  have hNorm : ‖Right‖ ≤ ‖F‖ := by
    simpa [Right] using
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightWilsonSourceBCF_norm_le
        H N latticeSpacing n J hJ r hr F
  have hTerm : 2 * ‖Right‖ ≤ 2 * ‖F‖ := by
    nlinarith
  have hCardNat :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightSupport_card_le
      H latticeSpacing n J r
  have hCard :
      ((periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightSupport
        H latticeSpacing n J r).card : ℝ) ≤ 4 * (J.card : ℝ) := by
    exact_mod_cast hCardNat
  calc
    (∑ e ∈
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightSupport
          H latticeSpacing n J r,
      2 * ‖periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightWilsonSourceBCF
        H N latticeSpacing n J hJ r hr F‖) ≤
      ∑ _e ∈
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightSupport
          H latticeSpacing n J r,
        2 * ‖F‖ := by
          apply Finset.sum_le_sum
          intro e he
          simpa [Right] using hTerm
    _ =
      ((periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightSupport
        H latticeSpacing n J r).card : ℝ) * (2 * ‖F‖) := by simp
    _ ≤ (4 * (J.card : ℝ)) * (2 * ‖F‖) :=
      mul_le_mul_of_nonneg_right hCard (by positivity)
    _ = 8 * (J.card : ℝ) * ‖F‖ := by ring

/-- The reflected-left support sum has the same scale- and volume-independent
bound. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftReflectedSupport_sum_two_mul_sourceNorm_le
    (H N : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (hJ : ∀ q : ℚ, q ∈ J → 0 ≤ q)
    (F : BoundedContinuousFunction (∀ q : J, ℝ) ℝ) :
    (∑ e ∈
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftReflectedSupport
          H latticeSpacing n J,
      2 * ‖periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftWilsonSourceBCF
        H N latticeSpacing n J hJ F‖) ≤
      8 * (J.card : ℝ) * ‖F‖ := by
  let Left :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftWilsonSourceBCF
      H N latticeSpacing n J hJ F
  have hNorm : ‖Left‖ ≤ ‖F‖ := by
    simpa [Left] using
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftWilsonSourceBCF_norm_le
        H N latticeSpacing n J hJ F
  have hTerm : 2 * ‖Left‖ ≤ 2 * ‖F‖ := by
    nlinarith
  have hCardNat :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftReflectedSupport_card_le
      H latticeSpacing n J
  have hCard :
      ((periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftReflectedSupport
        H latticeSpacing n J).card : ℝ) ≤ 4 * (J.card : ℝ) := by
    exact_mod_cast hCardNat
  calc
    (∑ e ∈
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftReflectedSupport
          H latticeSpacing n J,
      2 * ‖periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftWilsonSourceBCF
        H N latticeSpacing n J hJ F‖) ≤
      ∑ _e ∈
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftReflectedSupport
          H latticeSpacing n J,
        2 * ‖F‖ := by
          apply Finset.sum_le_sum
          intro e he
          simpa [Left] using hTerm
    _ =
      ((periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftReflectedSupport
        H latticeSpacing n J).card : ℝ) * (2 * ‖F‖) := by simp
    _ ≤ (4 * (J.card : ℝ)) * (2 * ‖F‖) :=
      mul_le_mul_of_nonneg_right hCard (by positivity)
    _ = 8 * (J.card : ℝ) * ‖F‖ := by ring

/-- The actual finite midpoint Wilson-source covariance has a geometric decay
bound whose non-geometric prefactor is independent of lattice volume, spacing,
and midpoint translation. -/
set_option maxHeartbeats 800000 in
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointWilsonSourceCovariance_abs_le_geometric_uniformPrefactor_of_floor_min_ge
    (H N D : ℕ)
    (hH : 0 < H)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hThreshold : 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta < 1)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (hJ : ∀ q : ℚ, q ∈ J → 0 ≤ q)
    (r : ℚ)
    (hr : 0 ≤ r)
    (hleftWithin : ∀ q : ℚ, q ∈ J →
      Int.toNat
          (physicalTemporalFloorStep latticeSpacing ((q : ℚ) : ℝ) n) ≤ H)
    (hrightWithin : ∀ q : ℚ, q ∈ J →
      Int.toNat
          (physicalTemporalFloorStep latticeSpacing ((((q + r) + r : ℚ) : ℝ)) n) ≤ H)
    (hfloor : ∀ qLeft : ℚ, qLeft ∈ J → ∀ qRight : ℚ, qRight ∈ J →
      D ≤
        min
          (Int.toNat
              (physicalTemporalFloorStep latticeSpacing ((qLeft : ℚ) : ℝ) n) +
            Int.toNat
              (physicalTemporalFloorStep latticeSpacing
                ((((qRight + r) + r : ℚ) : ℝ)) n))
          (PeriodicHypercubicEvenSideLength H -
            (Int.toNat
                (physicalTemporalFloorStep latticeSpacing ((qLeft : ℚ) : ℝ) n) +
              Int.toNat
                (physicalTemporalFloorStep latticeSpacing
                  ((((qRight + r) + r : ℚ) : ℝ)) n))))
    (F : BoundedContinuousFunction (∀ q : J, ℝ) ℝ) :
    |periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointWilsonSourceCovariance
        H N hN beta hbeta latticeSpacing n J r F| ≤
      ((18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta) ^ D /
        (1 - 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta)) *
        (8 * (J.card : ℝ) * ‖F‖) ^ 2 := by
  let rho : ℝ := 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta
  let Ddata :=
    periodicHypercubicSpecialUnitary_sparseDobrushinMatrixData_of_threshold
      (PeriodicHypercubicEvenSideLength H) N
      (by
        simp [PeriodicHypercubicEvenSideLength]
        omega)
      hN beta hbeta hThreshold
  let K : ℝ := 8 * (J.card : ℝ) * ‖F‖
  let Rsum : ℝ :=
    ∑ e ∈
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightSupport
        H latticeSpacing n J r,
      2 * ‖periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightWilsonSourceBCF
        H N latticeSpacing n J hJ r hr F‖
  let Lsum : ℝ :=
    ∑ e ∈
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftReflectedSupport
        H latticeSpacing n J,
      2 * ‖periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftWilsonSourceBCF
        H N latticeSpacing n J hJ F‖
  have hRsum : Rsum ≤ K := by
    simpa [Rsum, K] using
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightSupport_sum_two_mul_sourceNorm_le
        H N latticeSpacing n J hJ r hr F
  have hLsum : Lsum ≤ K := by
    simpa [Lsum, K] using
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftReflectedSupport_sum_two_mul_sourceNorm_le
        H N latticeSpacing n J hJ F
  have hRsumNonneg : 0 ≤ Rsum := by
    dsimp [Rsum]
    positivity
  have hLsumNonneg : 0 ≤ Lsum := by
    dsimp [Lsum]
    positivity
  have hKNonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  have hRhoNonneg : 0 ≤ rho := by
    simpa [rho, Ddata,
      periodicHypercubicSpecialUnitary_sparseDobrushinMatrixData_of_threshold] using
      Ddata.coefficient_nonneg
  have hGapNonneg : 0 ≤ 1 - rho := by
    exact le_of_lt (sub_pos.mpr (by simpa [rho] using hThreshold))
  have hCoeffNonneg : 0 ≤ rho ^ D / (1 - rho) :=
    div_nonneg (pow_nonneg hRhoNonneg D) hGapNonneg
  have hProduct : Rsum * Lsum ≤ K * K :=
    mul_le_mul hRsum hLsum hLsumNonneg hKNonneg
  have hCov :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointWilsonSourceCovariance_abs_le_geometric_of_floor_min_ge
      H N D hH hN beta hbeta hThreshold latticeSpacing n J hJ r hr
      hleftWithin hrightWithin hfloor F
  calc
    |periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointWilsonSourceCovariance
        H N hN beta hbeta latticeSpacing n J r F| ≤
      (rho ^ D / (1 - rho)) * Rsum * Lsum := by
        simpa [rho, Rsum, Lsum] using hCov
    _ = (rho ^ D / (1 - rho)) * (Rsum * Lsum) := by ring
    _ ≤ (rho ^ D / (1 - rho)) * (K * K) :=
      mul_le_mul_of_nonneg_left hProduct hCoeffNonneg
    _ =
      ((18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta) ^ D /
        (1 - 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta)) *
        (8 * (J.card : ℝ) * ‖F‖) ^ 2 := by
      simp [rho, K, pow_two]

end

end MathlibAnalytic
end MGAP4D
