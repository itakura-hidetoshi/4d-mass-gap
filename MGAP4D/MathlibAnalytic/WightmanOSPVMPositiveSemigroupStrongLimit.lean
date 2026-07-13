import MGAP4D.MathlibAnalytic.WightmanOSPVMPositiveSemigroupDifferenceQuotient
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter Set Topology MeasureTheory
open scoped InnerProductSpace

noncomputable section

/-- On positive times, the globally bounded quotient multiplier is pointwise
controlled by the bounded Hamiltonian target multiplier. -/
theorem pvmPositiveSemigroupDifferenceQuotientMultiplier_norm_le_target
    {t : ℝ} (ht : 0 < t)
    (f h : PVMBoundedBorelRealFunction)
    (hCoordinate : ∀ energy : ℝ,
      h.toFun energy = energy * f.toFun energy)
    (energy : ℝ) :
    ‖(pvmPositiveSemigroupDifferenceQuotientMultiplier
        t f h hCoordinate).toFun energy‖ ≤ ‖h.toFun energy‖ := by
  by_cases henergy : 0 ≤ energy
  · rw [pvmPositiveSemigroupDifferenceQuotientMultiplier_apply_of_pos
      ht f h hCoordinate henergy]
    calc
      ‖pvmSemigroupDifferenceQuotientScalar t energy * f.toFun energy‖ ≤
          ‖energy * f.toFun energy‖ :=
        pvmSemigroupDifferenceQuotientScalar_mul_norm_le ht henergy
      _ = ‖h.toFun energy‖ := by rw [hCoordinate energy]
  · have henergyNeg : energy < 0 := lt_of_not_ge henergy
    rw [pvmPositiveSemigroupDifferenceQuotientMultiplier_apply_of_neg
      ht f h hCoordinate henergyNeg]
    exact norm_nonneg _

/-- Restricting a bounded target multiplier to nonnegative energy preserves any
pointwise uniform bound. -/
theorem pvmPositiveEnergyRestrict_norm_le
    (h : PVMBoundedBorelRealFunction)
    (C : ℝ) (hC : 0 ≤ C)
    (hBound : ∀ energy : ℝ, ‖h.toFun energy‖ ≤ C)
    (energy : ℝ) :
    ‖(pvmPositiveEnergyRestrict h).toFun energy‖ ≤ C := by
  by_cases henergy : 0 ≤ energy
  · simpa [pvmPositiveEnergyRestrict, pvmBoundedBorelRestrict, henergy]
      using hBound energy
  · simp [pvmPositiveEnergyRestrict, pvmBoundedBorelRestrict, henergy, hC]

/-- The positive-energy semigroup difference-quotient family satisfies the
actual compact/tail convergence predicate for the completed ambient PVM
integral.  Both integrated tails are discharged from quadratic PVM projection
tail continuity; no abstract tail hypothesis remains. -/
theorem pvmPositiveSemigroupDifferenceQuotientMultiplier_compactTailTendstoAtVector
    {M : ExplicitWightmanOSReconstructedModel}
    (A : ExplicitWightmanOSQuadraticPVMCountableAdditivity M)
    (f h : PVMBoundedBorelRealFunction)
    (hCoordinate : ∀ energy : ℝ,
      h.toFun energy = energy * f.toFun energy)
    (ψ : M.H) :
    PVMBoundedBorelCompactTailTendstoAtVector
      M.spectralPVM
      (nhdsWithin 0 (Set.Ioi 0))
      (fun t =>
        pvmPositiveSemigroupDifferenceQuotientMultiplier
          t f h hCoordinate)
      (pvmPositiveEnergyRestrict h)
      ψ := by
  intro ε hε
  obtain ⟨C, hBoundH⟩ := h.bounded_toFun
  have hC : 0 ≤ C :=
    le_trans (norm_nonneg (h.toFun 0)) (hBoundH 0)
  have hCOne : 0 < C + 1 := by linarith
  have hδ : 0 < ε / (4 * (C + 1)) := by positivity
  have hEventuallyProjection :=
    quadraticPVM_projection_natEnergyTail_eventually_small A ψ hδ
  obtain ⟨n, hnProjection⟩ := hEventuallyProjection.exists
  let R : ℝ := n
  have hR : 0 ≤ R := by simp [R]
  refine ⟨R, hR, ?_, ?_, ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have htPos : 0 < t := by simpa using ht
    have hBoundF : ∀ energy : ℝ,
        ‖(pvmPositiveSemigroupDifferenceQuotientMultiplier
            t f h hCoordinate).toFun energy‖ ≤ C := by
      intro energy
      exact
        (pvmPositiveSemigroupDifferenceQuotientMultiplier_norm_le_target
          htPos f h hCoordinate energy).trans (hBoundH energy)
    have hIntegral :=
      pvmBoundedBorelSpectralIntegralOperator_restrict_norm_le
        M.spectralPVM
        (pvmNatEnergyTail n)
        (measurableSet_pvmNatEnergyTail n)
        (pvmPositiveSemigroupDifferenceQuotientMultiplier
          t f h hCoordinate)
        C hC hBoundF ψ
    have hTail :
        ‖pvmBoundedBorelSpectralIntegralOperator M.spectralPVM
            (pvmBoundedBorelRestrict
              (pvmNatEnergyTail n)
              (measurableSet_pvmNatEnergyTail n)
              (pvmPositiveSemigroupDifferenceQuotientMultiplier
                t f h hCoordinate)) ψ‖ < ε / 4 := by
      apply hIntegral.trans_lt
      calc
        C * ‖M.spectralPVM.projection (pvmNatEnergyTail n) ψ‖ ≤
            (C + 1) *
              ‖M.spectralPVM.projection (pvmNatEnergyTail n) ψ‖ := by
          gcongr
          linarith
        _ < (C + 1) * (ε / (4 * (C + 1))) :=
          mul_lt_mul_of_pos_left hnProjection hCOne
        _ = ε / 4 := by field_simp [hCOne.ne']
    simpa [R, pvmNatEnergyTail] using hTail
  · have hBoundTarget : ∀ energy : ℝ,
        ‖(pvmPositiveEnergyRestrict h).toFun energy‖ ≤ C :=
      pvmPositiveEnergyRestrict_norm_le h C hC hBoundH
    have hIntegral :=
      pvmBoundedBorelSpectralIntegralOperator_restrict_norm_le
        M.spectralPVM
        (pvmNatEnergyTail n)
        (measurableSet_pvmNatEnergyTail n)
        (pvmPositiveEnergyRestrict h)
        C hC hBoundTarget ψ
    have hTail :
        ‖pvmBoundedBorelSpectralIntegralOperator M.spectralPVM
            (pvmBoundedBorelRestrict
              (pvmNatEnergyTail n)
              (measurableSet_pvmNatEnergyTail n)
              (pvmPositiveEnergyRestrict h)) ψ‖ < ε / 4 := by
      apply hIntegral.trans_lt
      calc
        C * ‖M.spectralPVM.projection (pvmNatEnergyTail n) ψ‖ ≤
            (C + 1) *
              ‖M.spectralPVM.projection (pvmNatEnergyTail n) ψ‖ := by
          gcongr
          linarith
        _ < (C + 1) * (ε / (4 * (C + 1))) :=
          mul_lt_mul_of_pos_left hnProjection hCOne
        _ = ε / 4 := by field_simp [hCOne.ne']
    simpa [R, pvmNatEnergyTail] using hTail
  · have hCompactEpsilon :
        0 < ε / (8 * (‖ψ‖ + 1)) := by positivity
    exact
      pvmPositiveSemigroupDifferenceQuotientMultiplier_eventually_uniformOn_energyWindow
        f h hCoordinate R hR hCompactEpsilon

/-- The actual completed ambient PVM integrals of the positive-energy semigroup
difference quotients converge strongly at every vector to the completed integral
of the positive-energy Hamiltonian target. -/
theorem pvmPositiveSemigroupDifferenceQuotientSpectralIntegral_tendsto
    {M : ExplicitWightmanOSReconstructedModel}
    (A : ExplicitWightmanOSQuadraticPVMCountableAdditivity M)
    (f h : PVMBoundedBorelRealFunction)
    (hCoordinate : ∀ energy : ℝ,
      h.toFun energy = energy * f.toFun energy)
    (ψ : M.H) :
    Tendsto
      (fun t : ℝ =>
        pvmBoundedBorelSpectralIntegralOperator M.spectralPVM
          (pvmPositiveSemigroupDifferenceQuotientMultiplier
            t f h hCoordinate) ψ)
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (pvmBoundedBorelSpectralIntegralOperator M.spectralPVM
        (pvmPositiveEnergyRestrict h) ψ)) := by
  exact
    pvmBoundedBorelSpectralIntegralOperator_tendsto_atVector_of_compactTail
      M.spectralPVM ψ
      (pvmPositiveSemigroupDifferenceQuotientMultiplier_compactTailTendstoAtVector
        A f h hCoordinate ψ)

end

end MathlibAnalytic
end MGAP4D
