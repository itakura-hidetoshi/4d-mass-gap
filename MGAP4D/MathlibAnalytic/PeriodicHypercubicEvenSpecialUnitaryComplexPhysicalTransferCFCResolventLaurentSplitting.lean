import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferCFCResolventTopPole
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Module End Set
open scoped InnerProductSpace InnerProduct Ring Topology

noncomputable section

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 750000

local instance periodicHypercubicEvenSpecialUnitaryComplexLaurentRealCompleteSpace
    (H N : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H N).completeSpace_coe

local instance periodicHypercubicEvenSpecialUnitaryComplexLaurentComplexCompleteSpace
    (H N : ℕ) :
    CompleteSpace (PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :=
  periodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert_completeSpace H N

/-- Every complex spectral parameter whose real part lies above the exact
excited-sector norm belongs to the resolvent set of the centered complex
transfer. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator_mem_resolventSet_of_excitedNorm_lt_re
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (z : ℂ)
    (hzq :
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta‖ < z.re) :
    z ∈ resolventSet ℂ
      (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator
        H N hN beta hbeta) := by
  let R := periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator
    H N hN beta hbeta
  have hRnorm :
      ‖R‖ =
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖ := by
    simpa [R] using
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator_norm_eq_real_excited
        H N hN beta hbeta
  have hzNorm : ‖R‖ < ‖z‖ := by
    calc
      ‖R‖ =
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
            H N hN beta hbeta‖ := hRnorm
      _ < z.re := hzq
      _ ≤ |z.re| := le_abs_self _
      _ ≤ ‖z‖ := Complex.abs_re_le_norm z
  have hOne :
      ‖(1 : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →L[ℂ]
        PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simp
  have hzNormMul :
      ‖R‖ *
          ‖(1 : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →L[ℂ]
            PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N)‖ < ‖z‖ := by
    calc
      ‖R‖ *
          ‖(1 : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →L[ℂ]
            PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N)‖ ≤
          ‖R‖ * 1 := mul_le_mul_of_nonneg_left hOne (norm_nonneg R)
      _ = ‖R‖ := by rw [mul_one]
      _ < ‖z‖ := hzNorm
  exact spectrum.mem_resolventSet_of_norm_lt_mul (a := R) (k := z) hzNormMul

/-- In particular the centered block is regular at the isolated top spectral
point `1`; its norm is strictly below that point. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator_one_mem_resolventSet
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    (1 : ℂ) ∈ resolventSet ℂ
      (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator
        H N hN beta hbeta) := by
  let R := periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator
    H N hN beta hbeta
  have hnorm : ‖R‖ < 1 := by
    simpa [R] using
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator_norm_lt_one
        H N hN beta hbeta
  have hOne :
      ‖(1 : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →L[ℂ]
        PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simp
  have hnormMul :
      ‖R‖ *
          ‖(1 : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →L[ℂ]
            PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N)‖ < ‖(1 : ℂ)‖ := by
    calc
      ‖R‖ *
          ‖(1 : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →L[ℂ]
            PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N)‖ ≤
          ‖R‖ * 1 := mul_le_mul_of_nonneg_left hOne (norm_nonneg R)
      _ = ‖R‖ := by rw [mul_one]
      _ < 1 := hnorm
      _ = ‖(1 : ℂ)‖ := by simp
  exact spectrum.mem_resolventSet_of_norm_lt_mul (a := R) (k := (1 : ℂ)) hnormMul

/-- On the punctured right-half-plane resolvent region, the full resolvent
restricted to the CFC-top complement is exactly the centered resolvent
restricted to that complement. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_resolvent_mul_cfcTopComplement_eq_centered_resolvent
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (z : ℂ)
    (hzq :
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta‖ < z.re)
    (hz1 : z ≠ 1) :
    resolvent
        (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta) z *
      (1 - periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta hbeta) =
    resolvent
        (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator
          H N hN beta hbeta) z *
      (1 - periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta hbeta) := by
  let S := periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let P := periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
    H N hN beta hbeta
  let R := periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator
    H N hN beta hbeta
  let Q := (1 : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →L[ℂ]
    PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) - P
  have hPP : P * P = P := by
    simpa [P] using
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_mul_self
        H N hN beta hbeta
  have hPR : P * R = 0 := by
    simpa [P, R] using
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_mul_centeredTransferOperator
        H N hN beta hbeta
  have hRP : R * P = 0 := by
    simpa [P, R] using
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator_mul_cfcTopProjection
        H N hN beta hbeta
  have hPQ : P * Q = 0 := by
    simp [Q, mul_sub, hPP]
  have hDecomp : S = P + R := by
    simp [S, P, R,
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator]
  have hzS : z ∈ resolventSet ℂ S := by
    apply
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rightHalfPlane_except_one_subset_complex_resolventSet
        H N hN beta hbeta
    exact ⟨by simpa [S] using hzq, hz1⟩
  have hzR : z ∈ resolventSet ℂ R := by
    simpa [R] using
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator_mem_resolventSet_of_excitedNorm_lt_re
        H N hN beta hbeta z hzq
  have hzSUnit : IsUnit
      (algebraMap ℂ
          (PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →L[ℂ]
            PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) z - S) := hzS
  have hzRUnit : IsUnit
      (algebraMap ℂ
          (PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →L[ℂ]
            PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) z - R) := hzR
  have hz0 : z ≠ 0 := by
    intro hz
    subst z
    have hneg :
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖ < 0 := by
      simpa using hzq
    have hnonneg :
        0 ≤ ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖ := by
      positivity
    exact (not_lt_of_ge hnonneg) hneg
  have hPB :
      P * (algebraMap ℂ
          (PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →L[ℂ]
            PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) z - R) =
        z • P := by
    calc
      P * (algebraMap ℂ
          (PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →L[ℂ]
            PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) z - R) =
          P * algebraMap ℂ
            (PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →L[ℂ]
              PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) z - P * R := by
        rw [mul_sub]
      _ = P * algebraMap ℂ
            (PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →L[ℂ]
              PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) z := by
        rw [hPR, sub_zero]
      _ = z • P := by
        apply ContinuousLinearMap.ext
        intro x
        simp
  have hPResR : z • (P * resolvent R z) = P := by
    calc
      z • (P * resolvent R z) = (z • P) * resolvent R z := by
        apply ContinuousLinearMap.ext
        intro x
        simp
      _ = (P * (algebraMap ℂ
            (PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →L[ℂ]
              PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) z - R)) *
            resolvent R z := by rw [hPB]
      _ = P := by
        rw [mul_assoc, resolvent, Ring.mul_inverse_cancel _ hzRUnit, mul_one]
  have hPresRQ : P * (resolvent R z * Q) = 0 := by
    have hzeroSmul : z • (P * (resolvent R z * Q)) = 0 := by
      calc
        z • (P * (resolvent R z * Q)) =
            (z • (P * resolvent R z)) * Q := by
          apply ContinuousLinearMap.ext
          intro x
          simp
        _ = P * Q := by rw [hPResR]
        _ = 0 := hPQ
    rcases eq_zero_or_eq_zero_of_smul_eq_zero hzeroSmul with hz | hzero
    · exact (hz0 hz).elim
    · exact hzero
  have hShiftEq :
      algebraMap ℂ
          (PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →L[ℂ]
            PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) z - S =
        (algebraMap ℂ
            (PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →L[ℂ]
              PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) z - R) - P := by
    rw [hDecomp]
    abel
  have hBResRQ :
      (algebraMap ℂ
          (PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →L[ℂ]
            PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) z - R) *
        (resolvent R z * Q) = Q := by
    rw [← mul_assoc, resolvent, Ring.mul_inverse_cancel _ hzRUnit, one_mul]
  have hRightInvQ :
      (algebraMap ℂ
          (PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →L[ℂ]
            PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) z - S) *
        (resolvent R z * Q) = Q := by
    rw [hShiftEq, sub_mul, hBResRQ, hPresRQ, sub_zero]
  have hReg : resolvent S z * Q = resolvent R z * Q := by
    rw [resolvent]
    exact
      (Ring.inverse_mul_eq_iff_eq_mul
        (algebraMap ℂ
            (PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →L[ℂ]
              PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) z - S)
        Q
        ((algebraMap ℂ
              (PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →L[ℂ]
                PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) z - R)⁻¹ʳ * Q)
        hzSUnit).2 (by
          simpa [resolvent] using hRightInvQ.symm)
  simpa [S, P, R, Q] using hReg

/-- Full rank-free Laurent splitting of the genuine complex normalized Wilson
transfer resolvent near the isolated top spectral point: the only top-sector
singular term is `(z-1)⁻¹ P_CFC`, while the complement is the centered
resolvent block. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_resolvent_eq_topPole_add_centered
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (z : ℂ)
    (hzq :
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta‖ < z.re)
    (hz1 : z ≠ 1) :
    resolvent
        (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta) z =
      (z - 1)⁻¹ •
          periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
            H N hN beta hbeta +
        resolvent
            (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator
              H N hN beta hbeta) z *
          (1 - periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
            H N hN beta hbeta) := by
  let S := periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let P := periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
    H N hN beta hbeta
  let R := periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator
    H N hN beta hbeta
  let Q := (1 : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →L[ℂ]
    PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) - P
  have hResidue : (z - 1) • (resolvent S z * P) = P := by
    simpa [S, P] using
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_resolvent_mul_cfcTop_residue
        H N hN beta hbeta z hzq hz1
  have hTop : resolvent S z * P = (z - 1)⁻¹ • P := by
    calc
      resolvent S z * P =
          ((z - 1)⁻¹ * (z - 1)) • (resolvent S z * P) := by
        rw [inv_mul_cancel₀ (sub_ne_zero.mpr hz1), one_smul]
      _ = (z - 1)⁻¹ • ((z - 1) • (resolvent S z * P)) := by
        rw [← smul_smul]
      _ = (z - 1)⁻¹ • P := by rw [hResidue]
  have hReg : resolvent S z * Q = resolvent R z * Q := by
    simpa [S, P, R, Q] using
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_resolvent_mul_cfcTopComplement_eq_centered_resolvent
        H N hN beta hbeta z hzq hz1
  have hPQsum : P + Q = 1 := by
    simp [Q]
  calc
    resolvent S z = resolvent S z * 1 := by rw [mul_one]
    _ = resolvent S z * (P + Q) := by rw [hPQsum]
    _ = resolvent S z * P + resolvent S z * Q := by rw [mul_add]
    _ = (z - 1)⁻¹ • P + resolvent R z * Q := by rw [hTop, hReg]
    _ = _ := by rfl

/-- Audit-visible full Laurent package: the centered block is regular at `1`,
and every point in the punctured right-half-plane has the exact top-pole plus
centered-resolvent decomposition. -/
structure PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferCFCResolventLaurentPackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) : Prop where
  centeredRegularAtOne :
    (1 : ℂ) ∈ resolventSet ℂ
      (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator
        H N hN beta hbeta)
  laurentSplitting :
    ∀ z : ℂ,
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖ < z.re →
      z ≠ 1 →
      resolvent
          (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
            H N hN beta hbeta) z =
        (z - 1)⁻¹ •
            periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
              H N hN beta hbeta +
          resolvent
              (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator
                H N hN beta hbeta) z *
            (1 - periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
              H N hN beta hbeta)

/-- Construct the exact rank-free resolvent Laurent package. -/
theorem periodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferCFCResolventLaurentPackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferCFCResolventLaurentPackage
      H N hN beta hbeta :=
  { centeredRegularAtOne :=
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator_one_mem_resolventSet
        H N hN beta hbeta
    laurentSplitting :=
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_resolvent_eq_topPole_add_centered
        H N hN beta hbeta }

end
end MathlibAnalytic
end MGAP4D