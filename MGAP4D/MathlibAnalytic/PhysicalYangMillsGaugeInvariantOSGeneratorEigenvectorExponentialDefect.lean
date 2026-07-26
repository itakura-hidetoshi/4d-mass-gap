import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSMovingExponentialDifferenceQuotient
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRightHamiltonianSemigroupCovariance
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology

/-- For a fixed positive energy, the normalized right exponential defect has
slope equal to that energy. -/
theorem tendsto_nnreal_inv_mul_one_sub_exp_neg_fixed
    {energy : ℝ}
    (henergy : 0 < energy) :
    Tendsto
      (fun t : NNReal =>
        ((t : NNReal) : ℝ)⁻¹ *
          (1 - Real.exp (-energy * (((t : NNReal) : ℝ)))))
      (nhdsWithin 0 (Ioi 0))
      (nhds energy) := by
  have hcoe_nhds :
      Tendsto
        (fun t : NNReal => (((t : NNReal) : ℝ)))
        (nhdsWithin 0 (Ioi 0))
        (nhds 0) :=
    (continuous_subtype_val.tendsto (0 : NNReal)).mono_left inf_le_left
  have hproduct_nhds :
      Tendsto
        (fun t : NNReal => (((t : NNReal) : ℝ)) * energy)
        (nhdsWithin 0 (Ioi 0))
        (nhds 0) := by
    simpa using hcoe_nhds.mul tendsto_const_nhds
  have hproduct_pos :
      ∀ᶠ t : NNReal in nhdsWithin 0 (Ioi 0),
        (((t : NNReal) : ℝ)) * energy ∈ Ioi (0 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact mul_pos (by exact_mod_cast ht) henergy
  have hproduct_within :
      Tendsto
        (fun t : NNReal => (((t : NNReal) : ℝ)) * energy)
        (nhdsWithin 0 (Ioi 0))
        (nhdsWithin 0 (Ioi 0)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      (fun t : NNReal => (((t : NNReal) : ℝ)) * energy)
      hproduct_nhds hproduct_pos
  have hratio :
      Tendsto
        (fun t : NNReal =>
          ((((t : NNReal) : ℝ)) * energy)⁻¹ *
            (1 - Real.exp (-((((t : NNReal) : ℝ)) * energy))))
        (nhdsWithin 0 (Ioi 0))
        (nhds 1) :=
    tendsto_real_inv_mul_one_sub_exp_neg.comp hproduct_within
  have hfunction :
      (fun t : NNReal =>
        ((t : NNReal) : ℝ)⁻¹ *
          (1 - Real.exp (-energy * (((t : NNReal) : ℝ))))) =
      (fun t : NNReal =>
        energy *
          (((((t : NNReal) : ℝ)) * energy)⁻¹ *
            (1 - Real.exp (-((((t : NNReal) : ℝ)) * energy))))) := by
    funext t
    by_cases ht : (((t : NNReal) : ℝ)) = 0
    · simp [ht]
    · have he : energy ≠ 0 := ne_of_gt henergy
      have hexponent :
          -energy * (((t : NNReal) : ℝ)) =
            -((((t : NNReal) : ℝ)) * energy) := by
        ring
      rw [hexponent]
      field_simp [ht, he]
  rw [hfunction]
  simpa using (tendsto_const_nhds.mul hratio)

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- A right-Hamiltonian eigenvector remains an eigenvector with the same energy
under every positive-time semigroup operator. -/
theorem HasRightHamiltonianValue.operator_eigenvector
    (T : P.StronglyContinuousPhysicalSemigroup)
    {psi : P.PhysicalHilbert}
    {energy : ℝ}
    (h : T.HasRightHamiltonianValue psi (energy • psi))
    (s : NNReal) :
    T.HasRightHamiltonianValue
      (T.toPhysicalSemigroup.operator s psi)
      (energy • T.toPhysicalSemigroup.operator s psi) := by
  have hs := h.operator T s
  simpa only [map_smul] using hs

/-- A positive-energy right-Hamiltonian eigenvector has an `o(t)` defect from
its scalar exponential model at time zero. -/
theorem HasRightHamiltonianValue.exponentialModelDefect_tendsto_zero
    (T : P.StronglyContinuousPhysicalSemigroup)
    {psi : P.PhysicalHilbert}
    {energy : ℝ}
    (henergy : 0 < energy)
    (h : T.HasRightHamiltonianValue psi (energy • psi)) :
    Tendsto
      (fun t : NNReal =>
        (((t : NNReal) : ℝ))⁻¹ •
          (Real.exp (-energy * (((t : NNReal) : ℝ))) • psi -
            T.toPhysicalSemigroup.operator t psi))
      (nhdsWithin 0 (Ioi 0))
      (nhds 0) := by
  have hhamiltonian :
      Tendsto
        (fun t : NNReal => T.rightHamiltonianDifferenceQuotient psi t)
        (nhdsWithin 0 (Ioi 0))
        (nhds (energy • psi)) := by
    unfold HasRightHamiltonianValue HasRightGeneratorValue at h
    have hneg := h.neg
    simpa only [rightHamiltonianDifferenceQuotient_eq_neg, neg_neg] using hneg
  have hslope := tendsto_nnreal_inv_mul_one_sub_exp_neg_fixed henergy
  have hscalarVector :
      Tendsto
        (fun t : NNReal =>
          ((((t : NNReal) : ℝ))⁻¹ *
            (1 - Real.exp (-energy * (((t : NNReal) : ℝ))))) • psi)
        (nhdsWithin 0 (Ioi 0))
        (nhds (energy • psi)) := by
    simpa using hslope.smul (tendsto_const_nhds :
      Tendsto (fun _ : NNReal => psi)
        (nhdsWithin 0 (Ioi 0)) (nhds psi))
  have hsub := hhamiltonian.sub hscalarVector
  have hfunction :
      (fun t : NNReal =>
        (((t : NNReal) : ℝ))⁻¹ •
          (Real.exp (-energy * (((t : NNReal) : ℝ))) • psi -
            T.toPhysicalSemigroup.operator t psi)) =
      (fun t : NNReal =>
        T.rightHamiltonianDifferenceQuotient psi t -
          ((((t : NNReal) : ℝ))⁻¹ *
            (1 - Real.exp (-energy * (((t : NNReal) : ℝ))))) • psi) := by
    funext t
    unfold rightHamiltonianDifferenceQuotient
    module
  rw [hfunction]
  simpa only [sub_self] using hsub

/-- The same local exponential-model defect holds at every point of the
semigroup orbit. -/
theorem HasRightHamiltonianValue.orbitExponentialModelDefect_tendsto_zero
    (T : P.StronglyContinuousPhysicalSemigroup)
    {psi : P.PhysicalHilbert}
    {energy : ℝ}
    (henergy : 0 < energy)
    (h : T.HasRightHamiltonianValue psi (energy • psi))
    (s : NNReal) :
    Tendsto
      (fun t : NNReal =>
        (((t : NNReal) : ℝ))⁻¹ •
          (Real.exp (-energy * (((t : NNReal) : ℝ))) •
              T.toPhysicalSemigroup.operator s psi -
            T.toPhysicalSemigroup.operator t
              (T.toPhysicalSemigroup.operator s psi)))
      (nhdsWithin 0 (Ioi 0))
      (nhds 0) :=
  HasRightHamiltonianValue.exponentialModelDefect_tendsto_zero
    T henergy (h.operator_eigenvector T s)

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
