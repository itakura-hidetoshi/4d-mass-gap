import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSExponentialGapSlope
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRightHamiltonian
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology

/-- The normalized exponential defect has unit right slope at zero. -/
theorem tendsto_real_inv_mul_one_sub_exp_neg :
    Tendsto
      (fun z : ℝ => z⁻¹ * (1 - Real.exp (-z)))
      (nhdsWithin 0 (Ioi 0))
      (nhds 1) := by
  have hexp :
      HasDerivAt (fun z : ℝ => Real.exp (-(1 : ℝ) * z)) (-1) 0 := by
    simpa using
      ((hasDerivAt_const_mul (x := (0 : ℝ)) (-1 : ℝ)).exp)
  have hderiv :
      HasDerivAt (fun z : ℝ => 1 - Real.exp (-z)) 1 0 := by
    simpa using
      ((hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))).sub hexp)
  simpa [smul_eq_mul] using hderiv.tendsto_slope_zero_right

/-- If positive widths shrink to zero and positive energies converge, the moving
exponential difference quotient converges to the limiting energy. -/
theorem tendsto_nnreal_inv_mul_one_sub_exp_neg_moving
    {width : ℕ → NNReal}
    {energy : ℕ → ℝ}
    {limitEnergy : ℝ}
    (hwidth_pos : ∀ n, 0 < width n)
    (hwidth : Tendsto width atTop (nhdsWithin 0 (Ioi 0)))
    (henergy_pos : ∀ n, 0 < energy n)
    (henergy : Tendsto energy atTop (nhds limitEnergy)) :
    Tendsto
      (fun n =>
        ((width n : NNReal) : ℝ)⁻¹ *
          (1 - Real.exp (-energy n * (((width n : NNReal) : ℝ)))))
      atTop
      (nhds limitEnergy) := by
  have hwidth_nhds : Tendsto width atTop (nhds 0) :=
    hwidth.mono_right inf_le_left
  have hwidth_real :
      Tendsto (fun n => (((width n : NNReal) : ℝ))) atTop (nhds 0) :=
    (continuous_subtype_val.tendsto (0 : NNReal)).comp hwidth_nhds
  have hproduct :
      Tendsto
        (fun n => (((width n : NNReal) : ℝ)) * energy n)
        atTop (nhds 0) := by
    simpa using hwidth_real.mul henergy
  have hproduct_within :
      Tendsto
        (fun n => (((width n : NNReal) : ℝ)) * energy n)
        atTop (nhdsWithin 0 (Ioi 0)) := by
    rw [nhdsWithin]
    refine le_inf hproduct ?_
    rw [le_principal_iff]
    exact Filter.Eventually.of_forall fun n =>
      mul_pos (by exact_mod_cast hwidth_pos n) (henergy_pos n)
  have hratio :
      Tendsto
        (fun n =>
          ((((width n : NNReal) : ℝ)) * energy n)⁻¹ *
            (1 - Real.exp (-((((width n : NNReal) : ℝ)) * energy n))))
        atTop (nhds 1) :=
    tendsto_real_inv_mul_one_sub_exp_neg.comp hproduct_within
  have hfunction :
      (fun n =>
        (((width n : NNReal) : ℝ))⁻¹ *
          (1 - Real.exp (-energy n * (((width n : NNReal) : ℝ))))) =
      (fun n =>
        energy n *
          (((((width n : NNReal) : ℝ)) * energy n)⁻¹ *
            (1 - Real.exp (-((((width n : NNReal) : ℝ)) * energy n))))) := by
    funext n
    have hw : (((width n : NNReal) : ℝ)) ≠ 0 :=
      ne_of_gt (by exact_mod_cast hwidth_pos n)
    have he : energy n ≠ 0 := ne_of_gt (henergy_pos n)
    rw [mul_comm (energy n) (((width n : NNReal) : ℝ))]
    field_simp [hw, he]
  rw [hfunction]
  simpa using henergy.mul hratio

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- A moving exponential model and an `o(h)` semigroup intertwining defect imply
right-Hamiltonian difference-quotient compatibility. -/
theorem rightHamiltonianDifferenceQuotient_sub_energy_smul_tendsto_zero_of_exponentialModel
    (T : P.StronglyContinuousPhysicalSemigroup)
    {width : ℕ → NNReal}
    {energy : ℕ → ℝ}
    {limitEnergy : ℝ}
    {vectorSeq : ℕ → P.PhysicalHilbert}
    {vectorLimit : P.PhysicalHilbert}
    (hwidth_pos : ∀ n, 0 < width n)
    (hwidth : Tendsto width atTop (nhdsWithin 0 (Ioi 0)))
    (henergy_pos : ∀ n, 0 < energy n)
    (henergy : Tendsto energy atTop (nhds limitEnergy))
    (hvector : Tendsto vectorSeq atTop (nhds vectorLimit))
    (hmodelDefect :
      Tendsto
        (fun n =>
          (((width n : NNReal) : ℝ))⁻¹ •
            (Real.exp (-energy n * (((width n : NNReal) : ℝ))) • vectorSeq n -
              T.toPhysicalSemigroup.operator (width n) (vectorSeq n)))
        atTop (nhds 0)) :
    Tendsto
      (fun n =>
        T.rightHamiltonianDifferenceQuotient (vectorSeq n) (width n) -
          energy n • vectorSeq n)
      atTop (nhds 0) := by
  have hslope := tendsto_nnreal_inv_mul_one_sub_exp_neg_moving
    hwidth_pos hwidth henergy_pos henergy
  have hscalar :
      Tendsto
        (fun n =>
          (((width n : NNReal) : ℝ))⁻¹ *
              (1 - Real.exp (-energy n * (((width n : NNReal) : ℝ)))) -
            energy n)
        atTop (nhds 0) := by
    simpa only [sub_self] using hslope.sub henergy
  have hscalarVector :
      Tendsto
        (fun n =>
          ((((width n : NNReal) : ℝ))⁻¹ *
              (1 - Real.exp (-energy n * (((width n : NNReal) : ℝ)))) -
            energy n) • vectorSeq n)
        atTop (nhds 0) := by
    simpa only [zero_smul] using hscalar.smul hvector
  have hsum := hscalarVector.add hmodelDefect
  have hfunction :
      (fun n =>
        T.rightHamiltonianDifferenceQuotient (vectorSeq n) (width n) -
          energy n • vectorSeq n) =
      (fun n =>
        ((((width n : NNReal) : ℝ))⁻¹ *
              (1 - Real.exp (-energy n * (((width n : NNReal) : ℝ)))) -
            energy n) • vectorSeq n +
          (((width n : NNReal) : ℝ))⁻¹ •
            (Real.exp (-energy n * (((width n : NNReal) : ℝ))) • vectorSeq n -
              T.toPhysicalSemigroup.operator (width n) (vectorSeq n))) := by
    funext n
    unfold rightHamiltonianDifferenceQuotient
    module
  rw [hfunction]
  simpa only [zero_add] using hsum

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
