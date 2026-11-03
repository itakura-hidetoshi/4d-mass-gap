import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalTransferExplicitKernelFloorV5_PZ37AEJ
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumKernelHarnack
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AEK — original continuous vacuum quantitative global Harnack

The genuine Wilson kernel has the explicit finite-volume uniform interval
  k = exp (-beta * actionBudget H) <= K(A,B) <= 1.
The true continuous Perron vacuum Omega is represented by the original
nonnegative normalized physical top eigenvector. Its exact pointwise
Perron equation and original normalized Haar measure imply
  k * Omega(A) <= Omega(B) for all original spatial boundaries A,B.
The L2 norm-one identity then converts global comparability into explicit
absolute pointwise vacuum bounds.

This module adds genuine original SU(2) joint sqrt-density bounds, without
proxy densities, numerical net hypotheses or continuum mass-gap claims.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical InnerProductSpace BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37AEK_group (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4Q2PZ37AEK_compact (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4Q2PZ37AEK_countable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4Q2PZ37AEK_measurable (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4Q2PZ37AEK_borel (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4Q2PZ37AEK_links (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Genuine global pointwise comparability of the original continuous
Perron vacuum by the literal positive Wilson action floor. -/
theorem p4Q2PZ37AEK_originalContinuousVacuum_globalKernelRatio
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor H beta *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta B ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H N hN beta hbeta C := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let V := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
    H N hN beta hbeta
  let K := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta
  let Omega := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
    H N hN beta hbeta
  let lambda := ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖
  let k := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor H beta
  have hk : 0 ≤ k :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_pos
      H beta).le
  have hlam : 0 < lambda :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H N hN beta hbeta
  have hNonneg :
      ∀ᵐ A ∂μ, 0 ≤ V.1 A := by
    simpa only [V, μ] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_ae_nonnegative
        H N hN beta hbeta
  have hInt (D : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
      Integrable (fun A => V.1 A * K A D) μ := by
    simpa only [V, K, μ] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_mul_integrable
        H N hN beta hbeta
        ((V : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
          Lp ℝ 2 μ) D
  have hKernel (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
      k * K A B ≤ K A C := by
    calc
      k * K A B ≤ k * 1 :=
        mul_le_mul_of_nonneg_left
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_le_one
            H N hN beta hbeta A B) hk
      _ = k := mul_one k
      _ ≤ K A C :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_le_kernel
          H N hN beta hbeta A C
  have hPointwise : ∀ᵐ A ∂μ, k * (V.1 A * K A B) ≤ V.1 A * K A C := by
    filter_upwards [hNonneg] with A hA
    calc
      k * (V.1 A * K A B) = V.1 A * (k * K A B) := by ring
      _ ≤ V.1 A * K A C :=
        mul_le_mul_of_nonneg_left (hKernel A) hA
  have hIntegral :
      k * (∫ A, V.1 A * K A B ∂μ) ≤
        ∫ A, V.1 A * K A C ∂μ := by
    calc
      k * (∫ A, V.1 A * K A B ∂μ) =
          ∫ A, k * (V.1 A * K A B) ∂μ :=
        (integral_const_mul k _).symm
      _ ≤ ∫ A, V.1 A * K A C ∂μ :=
        integral_mono_ae ((hInt B).const_mul k) (hInt C) hPointwise
  have hPerron (D : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
      lambda * Omega D = ∫ A, V.1 A * K A D ∂μ := by
    exact periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_topNorm_mul_eq_integral_kernel
      H N hN beta hbeta D
  have hScaled : lambda * (k * Omega B) ≤ lambda * Omega C := by
    calc
      lambda * (k * Omega B) = k * (lambda * Omega B) := by ring
      _ = k * (∫ A, V.1 A * K A B ∂μ) := by rw [hPerron B]
      _ ≤ ∫ A, V.1 A * K A C ∂μ := hIntegral
      _ = lambda * Omega C := (hPerron C).symm
  exact (mul_le_mul_left hlam).mp hScaled


/-- A nonnegative probability-Haar L2 vector of norm one and a
global multiplicative Harnack comparison has explicit pointwise bounds.
This is a genuine L2 statement, not an arbitrary choice of representatives. -/
theorem p4Q2PZ37AEK_unitLp_globalRatio_givesPointwiseBounds
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → ℝ) (hf : MemLp f 2 μ)
    (hUnit : ‖hf.toLp f‖ = 1)
    (k : ℝ) (hk : 0 < k)
    (hPos : ∀ x, 0 ≤ f x)
    (hRatio : ∀ x y, k * f x ≤ f y) :
    ∀ x, k ≤ f x ∧ f x ≤ k⁻¹ := by
  intro x
  have hConstLo : MemLp (fun _ : α => k * f x) 2 μ := memLp_const _
  have hConstHi : MemLp (fun _ : α => f x / k) 2 μ := memLp_const _
  have hConstLoNorm :
      ‖hConstLo.toLp (fun _ : α => k * f x)‖ = k * f x := by
    rw [MemLp.toLp_const]
    have hNorm :=
      Lp.norm_const' (μ := μ) (p := (2 : ENNReal)) (c := k * f x)
        (by norm_num) (by norm_num)
    simpa [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hk.le (hPos x))]
      using hNorm
  have hConstHiNorm :
      ‖hConstHi.toLp (fun _ : α => f x / k)‖ = f x / k := by
    rw [MemLp.toLp_const]
    have hNorm :=
      Lp.norm_const' (μ := μ) (p := (2 : ENNReal)) (c := f x / k)
        (by norm_num) (by norm_num)
    simpa [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hPos x) hk.le)]
      using hNorm
  have hCompareLo :
      ‖hConstLo.toLp (fun _ : α => k * f x)‖ ≤ ‖hf.toLp f‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hConstLo.coeFn_toLp, hf.coeFn_toLp] with y h1 h2
    rw [h1, h2]
    simpa [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hk.le (hPos x)), abs_of_nonneg (hPos y)]
      using hRatio x y
  have hCompareHi :
      ‖hf.toLp f‖ ≤ ‖hConstHi.toLp (fun _ : α => f x / k)‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hf.coeFn_toLp, hConstHi.coeFn_toLp] with y h1 h2
    rw [h1, h2]
    have hxy : f y ≤ f x / k :=
      (le_div_iff₀ hk).2 (by simpa [mul_comm] using hRatio y x)
    simpa [Real.norm_eq_abs, abs_of_nonneg (hPos y),
      abs_of_nonneg (div_nonneg (hPos x) hk.le)] using hxy
  have hkfx : k * f x ≤ 1 := by
    calc
      k * f x = ‖hConstLo.toLp (fun _ : α => k * f x)‖ :=
        hConstLoNorm.symm
      _ ≤ ‖hf.toLp f‖ := hCompareLo
      _ = 1 := hUnit
  have hfx : 1 ≤ f x / k := by
    calc
      (1 : ℝ) = ‖hf.toLp f‖ := hUnit.symm
      _ ≤ ‖hConstHi.toLp (fun _ : α => f x / k)‖ := hCompareHi
      _ = f x / k := hConstHiNorm
  constructor
  · have h := (le_div_iff₀ hk).1 hfx
    simpa using h
  · have h : f x ≤ (1 : ℝ) / k :=
      (le_div_iff₀ hk).2 (by simpa [mul_comm] using hkfx)
    simpa only [one_div] using h

/-- The ORIGINAL continuous physical Perron vacuum, normalized to
the existing canonical Haar L2 top eigenvector of norm one, has the
pointwise interval k ≤ Omega(A) ≤ k⁻¹. This holds at every finite H
and positive rank, with the literal Wilson global action budget. -/
theorem p4Q2PZ37AEK_originalContinuousVacuum_explicitBounds
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ∀ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor H beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta A ∧
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta A ≤
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor H beta)⁻¹ := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let Omega := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
    H N hN beta hbeta
  let V := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
    H N hN beta hbeta
  let k := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor H beta
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
    infer_instance
  have hk : 0 < k :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_pos H beta
  have hOmegaPos : ∀ A, 0 ≤ Omega A := fun A =>
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H N hN beta hbeta A).le
  have hMem : MemLp Omega 2 μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_memLp_two
      H N hN beta hbeta
  have hEq : hMem.toLp Omega =
      ((V : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
        Lp ℝ 2 μ) := by
    apply Lp.ext
    exact hMem.coeFn_toLp.trans
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_ae_eq_existing
        H N hN beta hbeta)
  have hUnit : ‖hMem.toLp Omega‖ = 1 := by
    rw [hEq]
    change ‖V‖ = 1
    exact periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_norm
      H N hN beta hbeta
  have hRatio (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
      k * Omega A ≤ Omega B :=
    p4Q2PZ37AEK_originalContinuousVacuum_globalKernelRatio
      H N hN beta hbeta A B
  exact p4Q2PZ37AEK_unitLp_globalRatio_givesPointwiseBounds
    μ Omega hMem hUnit k hk hOmegaPos hRatio


/-- Real four-factor bound for the ORIGINAL normalized Wilson
joint density: if k<=lambda<=1, k<=Omega(left/right)<=1/k
and k<=K<=1, then k^3<=lambda^-1*Omega(left)*K*Omega(right)
<=k^-3. No independence or probabilistic replacement is used. -/
theorem p4Q2PZ37AEK_realWilsonJointWeightBounds
    (k lambda a c b : ℝ)
    (hk : 0 < k) (hkl : k ≤ lambda) (hl1 : lambda ≤ 1)
    (ha : k ≤ a ∧ a ≤ k⁻¹)
    (hc : k ≤ c ∧ c ≤ 1)
    (hb : k ≤ b ∧ b ≤ k⁻¹) :
    k ^ 3 ≤ lambda⁻¹ * (a * c * b) ∧
      lambda⁻¹ * (a * c * b) ≤ (k⁻¹) ^ 3 := by
  have hlpos : 0 < lambda := hk.trans_le hkl
  have hinvk : 0 ≤ k⁻¹ := inv_nonneg.mpr hk.le
  have hinvl : 0 ≤ lambda⁻¹ := inv_nonneg.mpr hlpos.le
  have ha0 : 0 ≤ a := hk.le.trans ha.1
  have hb0 : 0 ≤ b := hk.le.trans hb.1
  have hc0 : 0 ≤ c := hk.le.trans hc.1
  have hInvLo : (1 : ℝ) ≤ lambda⁻¹ := by
    have h := (inv_le_inv₀ (by norm_num : (0 : ℝ) < 1) hlpos).2 hl1
    simpa using h
  have hInvHi : lambda⁻¹ ≤ k⁻¹ :=
    (inv_le_inv₀ hk hlpos).2 hkl
  have hAcLo : k * k ≤ a * c :=
    mul_le_mul ha.1 hc.1 hk.le ha0
  have hAcHi : a * c ≤ k⁻¹ * 1 :=
    mul_le_mul ha.2 hc.2 hc0 hinvk
  have hAbcLo : (k * k) * k ≤ (a * c) * b :=
    mul_le_mul hAcLo hb.1 hk.le (mul_nonneg ha0 hc0)
  have hAbcHi : (a * c) * b ≤ (k⁻¹ * 1) * k⁻¹ :=
    mul_le_mul hAcHi hb.2 hb0 (mul_nonneg hinvk (by norm_num))
  constructor
  · calc
      k ^ 3 = (1 : ℝ) * ((k * k) * k) := by ring
      _ ≤ lambda⁻¹ * ((a * c) * b) :=
        mul_le_mul hInvLo hAbcLo
          (mul_nonneg (mul_nonneg hk.le hk.le) hk.le) hinvl
  · calc
      lambda⁻¹ * (a * c * b) ≤
          k⁻¹ * ((k⁻¹ * 1) * k⁻¹) :=
        mul_le_mul hInvHi hAbcHi
          (mul_nonneg (mul_nonneg ha0 hc0) hb0) hinvk
      _ = (k⁻¹) ^ 3 := by ring

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AEK_originalContinuousVacuum_globalKernelRatio

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AEK_unitLp_globalRatio_givesPointwiseBounds
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AEK_originalContinuousVacuum_explicitBounds

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AEK_realWilsonJointWeightBounds
