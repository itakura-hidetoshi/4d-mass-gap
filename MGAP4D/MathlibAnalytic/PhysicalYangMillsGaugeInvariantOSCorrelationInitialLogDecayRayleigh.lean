import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCorrelationHamiltonianRightSlope
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSSymmetricSemigroupCorrelationUnregularizedEffectiveMass
import Mathlib.Tactic

/-!
# Initial unregularized OS logarithmic decay and the Hamiltonian Rayleigh rate

The merged infinitesimal correlation/Hamiltonian bridge identifies

`(C_psi(0) - C_psi(t)) / t -> <H_right psi, psi>`

as positive Euclidean time tends to zero.  For a nonzero physical state and a
symmetric completed OS semigroup, every finite-time correlation is strictly
positive.  The elementary logarithmic tangent inequalities

`(x-y)/x <= log x - log y <= (x-y)/y`

for positive `x,y`, together with continuity `C_psi(t) -> C_psi(0)`, therefore
squeeze the unregularized logarithmic decay to

`<H_right psi, psi> / ||psi||^2`.

Equivalently, the zero-to-`t` unregularized effective-mass secant converges to
the Hamiltonian Rayleigh quotient at the initial Euclidean-time endpoint.

No spectral theorem, PVM construction, self-adjointness hypothesis, or new
physical assumption is used.
-/

namespace MGAP4D

open Filter Set Topology

/-- Tangent-line sandwich for the logarithmic difference of two positive real
numbers.  The statement is symmetric enough that no ordering of `x` and `y` is
required. -/
theorem log_sub_log_sandwich_of_pos
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (x - y) / x <= Real.log x - Real.log y ∧
      Real.log x - Real.log y <= (x - y) / y := by
  have hxy : Real.log (x / y) <= x / y - 1 := by
    by_cases hratio : x / y = 1
    · rw [hratio, Real.log_one]
      norm_num
    · exact (Real.log_lt_sub_one_of_pos (div_pos hx hy) hratio).le
  have hyx : Real.log (y / x) <= y / x - 1 := by
    by_cases hratio : y / x = 1
    · rw [hratio, Real.log_one]
      norm_num
    · exact (Real.log_lt_sub_one_of_pos (div_pos hy hx) hratio).le
  have hlogxy : Real.log (x / y) = Real.log x - Real.log y :=
    Real.log_div hx.ne' hy.ne'
  have hlogyx : Real.log (y / x) = Real.log y - Real.log x :=
    Real.log_div hy.ne' hx.ne'
  have hdivxy : x / y - 1 = (x - y) / y := by
    rw [sub_div, div_self hy.ne']
  have hdivyx : y / x - 1 = (y - x) / x := by
    rw [sub_div, div_self hx.ne']
  rw [hlogxy, hdivxy] at hxy
  rw [hlogyx, hdivyx] at hyx
  constructor
  · have hneg := neg_le_neg hyx
    calc
      (x - y) / x = -((y - x) / x) := by ring
      _ <= -(Real.log y - Real.log x) := hneg
      _ = Real.log x - Real.log y := by ring
  · exact hxy

namespace MathlibAnalytic

noncomputable section

open scoped InnerProductSpace

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- The initial unregularized logarithmic decay rate converges to the canonical
right-Hamiltonian energy divided by the zero-time correlation.

The proof is an order-theoretic squeeze between the raw correlation-loss slope
divided by `C_psi(0)` and the same slope divided by `C_psi(t)`. -/
theorem physicalCorrelationRealClampLog_rightSlope_tendsto_rightHamiltonian_overCorrelationZero
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : T.rightGeneratorDomain)
    (hpsi : (psi : P.PhysicalHilbert) ≠ 0) :
    Tendsto
      (fun t : NNReal =>
        (t : ℝ)⁻¹ *
          (T.physicalCorrelationRealClampLog
              (psi : P.PhysicalHilbert) 0 -
            T.physicalCorrelationRealClampLog
              (psi : P.PhysicalHilbert) (t : ℝ)))
      (nhdsWithin 0 (Ioi 0))
      (nhds
        (⟪T.rightHamiltonian psi,
            (psi : P.PhysicalHilbert)⟫_ℝ /
          T.physicalCorrelation (psi : P.PhysicalHilbert) 0)) := by
  let phi : P.PhysicalHilbert := (psi : P.PhysicalHilbert)
  let c0 : ℝ := T.physicalCorrelation phi 0
  let energy : ℝ := ⟪T.rightHamiltonian psi, phi⟫_ℝ
  change
    Tendsto
      (fun t : NNReal =>
        (t : ℝ)⁻¹ *
          (T.physicalCorrelationRealClampLog phi 0 -
            T.physicalCorrelationRealClampLog phi (t : ℝ)))
      (nhdsWithin 0 (Ioi 0))
      (nhds (energy / c0))
  have hc0pos : 0 < c0 := by
    dsimp [c0, phi]
    exact T.physicalCorrelation_pos_of_ne_zero hSymmetric 0 hpsi
  have hraw :
      Tendsto
        (fun t : NNReal =>
          (t : ℝ)⁻¹ * (c0 - T.physicalCorrelation phi t))
        (nhdsWithin 0 (Ioi 0))
        (nhds energy) := by
    simpa [c0, energy, phi] using
      T.physicalCorrelation_rightSlope_tendsto_rightHamiltonian_inner psi
  have hcorr :
      Tendsto
        (fun t : NNReal => T.physicalCorrelation phi t)
        (nhdsWithin 0 (Ioi 0))
        (nhds c0) := by
    exact
      (T.physicalCorrelation_continuous phi).continuousAt.mono_left inf_le_left
  have hlower :
      Tendsto
        (fun t : NNReal =>
          ((t : ℝ)⁻¹ * (c0 - T.physicalCorrelation phi t)) / c0)
        (nhdsWithin 0 (Ioi 0))
        (nhds (energy / c0)) :=
    hraw.div tendsto_const_nhds hc0pos.ne'
  have hupper :
      Tendsto
        (fun t : NNReal =>
          ((t : ℝ)⁻¹ * (c0 - T.physicalCorrelation phi t)) /
            T.physicalCorrelation phi t)
        (nhdsWithin 0 (Ioi 0))
        (nhds (energy / c0)) :=
    hraw.div hcorr hc0pos.ne'
  have hposTime :
      ∀ᶠ t : NNReal in nhdsWithin (0 : NNReal) (Ioi 0), 0 < t :=
    self_mem_nhdsWithin
  have hlower_le :
      ∀ᶠ t in nhdsWithin (0 : NNReal) (Ioi 0),
        ((t : ℝ)⁻¹ * (c0 - T.physicalCorrelation phi t)) / c0 <=
          (t : ℝ)⁻¹ *
            (Real.log c0 - Real.log (T.physicalCorrelation phi t)) := by
    filter_upwards [hposTime] with t ht
    have htReal : 0 < (t : ℝ) := by exact_mod_cast ht
    have hctpos : 0 < T.physicalCorrelation phi t := by
      dsimp [phi]
      exact T.physicalCorrelation_pos_of_ne_zero hSymmetric t hpsi
    have hsand := MGAP4D.log_sub_log_sandwich_of_pos hc0pos hctpos
    have hmul :=
      mul_le_mul_of_nonneg_left hsand.1 (inv_nonneg.mpr htReal.le)
    simpa [div_eq_mul_inv, mul_assoc] using hmul
  have hle_upper :
      ∀ᶠ t in nhdsWithin (0 : NNReal) (Ioi 0),
        (t : ℝ)⁻¹ *
            (Real.log c0 - Real.log (T.physicalCorrelation phi t)) <=
          ((t : ℝ)⁻¹ * (c0 - T.physicalCorrelation phi t)) /
            T.physicalCorrelation phi t := by
    filter_upwards [hposTime] with t ht
    have htReal : 0 < (t : ℝ) := by exact_mod_cast ht
    have hctpos : 0 < T.physicalCorrelation phi t := by
      dsimp [phi]
      exact T.physicalCorrelation_pos_of_ne_zero hSymmetric t hpsi
    have hsand := MGAP4D.log_sub_log_sandwich_of_pos hc0pos hctpos
    have hmul :=
      mul_le_mul_of_nonneg_left hsand.2 (inv_nonneg.mpr htReal.le)
    simpa [div_eq_mul_inv, mul_assoc] using hmul
  have hlogRaw :
      Tendsto
        (fun t : NNReal =>
          (t : ℝ)⁻¹ *
            (Real.log c0 - Real.log (T.physicalCorrelation phi t)))
        (nhdsWithin 0 (Ioi 0))
        (nhds (energy / c0)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      hlower hupper hlower_le hle_upper
  have hclampZero : T.physicalCorrelationRealClamp phi 0 = c0 := by
    simpa only [c0] using
      T.physicalCorrelationRealClamp_coe phi (0 : NNReal)
  simpa only [physicalCorrelationRealClampLog, hclampZero,
    T.physicalCorrelationRealClamp_coe] using hlogRaw

/-- Rayleigh-quotient form of the initial logarithmic decay theorem. -/
theorem physicalCorrelationRealClampLog_rightSlope_tendsto_rightHamiltonian_rayleigh
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : T.rightGeneratorDomain)
    (hpsi : (psi : P.PhysicalHilbert) ≠ 0) :
    Tendsto
      (fun t : NNReal =>
        (t : ℝ)⁻¹ *
          (T.physicalCorrelationRealClampLog
              (psi : P.PhysicalHilbert) 0 -
            T.physicalCorrelationRealClampLog
              (psi : P.PhysicalHilbert) (t : ℝ)))
      (nhdsWithin 0 (Ioi 0))
      (nhds
        (⟪T.rightHamiltonian psi,
            (psi : P.PhysicalHilbert)⟫_ℝ /
          ‖(psi : P.PhysicalHilbert)‖ ^ 2)) := by
  simpa only [T.physicalCorrelation_zero] using
    T.physicalCorrelationRealClampLog_rightSlope_tendsto_rightHamiltonian_overCorrelationZero
      hSymmetric psi hpsi

/-- The zero-to-`t` unregularized effective-mass secant converges at the initial
endpoint to the Hamiltonian Rayleigh quotient. -/
theorem physicalCorrelationRealClampEffectiveMass_zero_tendsto_rightHamiltonian_rayleigh
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : T.rightGeneratorDomain)
    (hpsi : (psi : P.PhysicalHilbert) ≠ 0) :
    Tendsto
      (fun t : NNReal =>
        T.physicalCorrelationRealClampEffectiveMass
          (psi : P.PhysicalHilbert) 0 (t : ℝ))
      (nhdsWithin 0 (Ioi 0))
      (nhds
        (⟪T.rightHamiltonian psi,
            (psi : P.PhysicalHilbert)⟫_ℝ /
          ‖(psi : P.PhysicalHilbert)‖ ^ 2)) := by
  simpa [physicalCorrelationRealClampEffectiveMass,
    MGAP4D.secantDecayRate, div_eq_mul_inv, mul_comm] using
    T.physicalCorrelationRealClampLog_rightSlope_tendsto_rightHamiltonian_rayleigh
      hSymmetric psi hpsi

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
