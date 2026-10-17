import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonFiberRieszDerivativeV5_JH
import MGAP4D.MathlibAnalytic.NonzeroDerivativeSmallPositive
import Mathlib.Tactic

/-!
# P4-Q2-JI: original two-context GI minor tangent is a spatial-Wilson determinant

The fixed genuine GI Haar-L2 functionals constructed in JH act on the
strong original fine-row derivative from JG. Constant pieces of that
derivative cancel in the two-context determinant. Its actual first
variation is minus half the determinant of the same original detector
applied to the true constant unit and spatial Wilson action.

The static spatial-action determinant is not asserted to be nonzero.
If it is nonzero at two actual contexts, the original raw-source minor
is nonzero throughout a sufficiently small positive fine-beta interval.
The norm-normalized physical-source minor differs only by a nonzero
inverse transfer norm: no derivative of that norm is assumed or needed.
This is a sufficient criterion, not a claim that the criterion holds.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000
local instance p4Q2JI_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2JI_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2JI_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2JI_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2JI_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
namespace GroundStatePosteriorJoint
section Frozen
variable (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "haar" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "L" => ContinuousMap.toLp 2 haar ℝ
local notation "G" => p4Q2JH_originalGIResponseCLM H b hb
local notation "F" => p4Q2JF_originalWilsonHaarRowContinuous H
local notation "D" => p4Q2JE_originalWilsonHaarZeroDerivativeLp H
local notation "kap" => p4Q2JE_originalWilsonHaarZeroDerivativeConstant H

noncomputable def p4Q2JI_actualSpatialWilsonContinuous : C(Cfg, ℝ) :=
  ⟨periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2,
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H 2⟩

/-- Exact splitting of the genuine Haar-L2 derivative; the two summands
are the actual spatial Wilson-action vector and actual constant vector. -/
theorem p4Q2JI_actualHaarL2Derivative_eq_spatialAction_and_constant :
    D = (-(1 / 2 : ℝ)) • L (p4Q2JI_actualSpatialWilsonContinuous H) -
      kap • L (1 : C(Cfg, ℝ)) := by
  have hC : p4Q2JE_originalWilsonHaarZeroDerivativeProfile H =
      (-(1 / 2 : ℝ)) • p4Q2JI_actualSpatialWilsonContinuous H -
        kap • (1 : C(Cfg, ℝ)) := by
    ext B
    change -(1 / 2 : ℝ) *
      periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2 B - kap =
      (-(1 / 2 : ℝ)) *
        periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2 B - kap * 1
    ring
  change L (p4Q2JE_originalWilsonHaarZeroDerivativeProfile H) = _
  rw [hC, map_sub, map_smul, map_smul]

/-- The same two genuine frozen Wilson detectors applied to the
constant unit and the original spatial Wilson action. -/
noncomputable def p4Q2JI_originalGISpatialActionMinor
    (e e' : Link) (z z' : Cfg × Cfg) : ℝ :=
  G e z (L (1 : C(Cfg, ℝ))) *
      G e' z' (L (p4Q2JI_actualSpatialWilsonContinuous H)) -
    G e z (L (p4Q2JI_actualSpatialWilsonContinuous H)) *
      G e' z' (L (1 : C(Cfg, ℝ)))

/-- Actual fine-row minor, using the unchanged original frozen Wilson
kernel and interacting posterior density contrast in both contexts. -/
noncomputable def p4Q2JI_originalGIRawFineRowMinor
    (e e' : Link) (z z' : Cfg × Cfg) (t : ℝ) : ℝ :=
  G e z (L (1 : C(Cfg, ℝ))) * G e' z' (L (F t)) -
    G e z (L (F t)) * G e' z' (L (1 : C(Cfg, ℝ)))

theorem p4Q2JI_originalGIRawFineRowMinor_zero
    (e e' : Link) (z z' : Cfg × Cfg) :
    p4Q2JI_originalGIRawFineRowMinor H b hb e e' z z' 0 = 0 := by
  have hF : F 0 = (1 : C(Cfg, ℝ)) := by
    ext B
    exact p4Q2IW_originalWilsonHaarRow_beta_zero H B
  unfold p4Q2JI_originalGIRawFineRowMinor
  rw [hF, sub_self]

/-- Strong differentiation passes through both actual original GI
functionals; the genuine Haar constant kap cancels from the minor. -/
theorem p4Q2JI_originalGIRawFineRowMinor_hasDerivAt_zero
    (e e' : Link) (z z' : Cfg × Cfg) :
    HasDerivAt (p4Q2JI_originalGIRawFineRowMinor H b hb e e' z z')
      (-(1 / 2 : ℝ) * p4Q2JI_originalGISpatialActionMinor H b hb e e' z z') 0 := by
  have hx := p4Q2JH_originalGIFineRow_hasDerivAt_zero H b hb e z
  have hy := p4Q2JH_originalGIFineRow_hasDerivAt_zero H b hb e' z'
  have hd := (hy.const_mul (G e z (L (1 : C(Cfg, ℝ))))).sub
    (hx.mul_const (G e' z' (L (1 : C(Cfg, ℝ)))))
  have hvalue : G e z (L (1 : C(Cfg, ℝ))) * G e' z' D -
      G e z D * G e' z' (L (1 : C(Cfg, ℝ))) =
      -(1 / 2 : ℝ) * p4Q2JI_originalGISpatialActionMinor H b hb e e' z z' := by
    rw [p4Q2JI_actualHaarL2Derivative_eq_spatialAction_and_constant H]
    simp only [map_sub, map_smul, smul_eq_mul]
    unfold p4Q2JI_originalGISpatialActionMinor
    ring
  exact hvalue ▸ hd

/-- A real nonzero static spatial-Wilson detector minor is sufficient
for the true raw fine-source GI minor to be nonzero at every coupling
in a fixed positive interval. The static nonzero witness remains OPEN. -/
theorem p4Q2JI_originalGIRawFineRowMinor_smallPositive_of_spatialMinor_ne
    (e e' : Link) (z z' : Cfg × Cfg)
    (hW : p4Q2JI_originalGISpatialActionMinor H b hb e e' z z' ≠ 0) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ t : ℝ, 0 < t → t < eps →
      p4Q2JI_originalGIRawFineRowMinor H b hb e e' z z' t ≠ 0 := by
  exact HasDerivAt.exists_pos_forall_pos_lt_ne_zero_of_eq_zero_of_ne_zero
    (p4Q2JI_originalGIRawFineRowMinor_hasDerivAt_zero H b hb e e' z z')
    (p4Q2JI_originalGIRawFineRowMinor_zero H b hb e e' z z')
    (mul_ne_zero (by norm_num) hW)

/-- The row's L2 vector is the actual unnormalized physical fine transfer
of the true Haar unit on the nonnegative physical coupling half-line. -/
theorem p4Q2JI_actualRawFineUnit_coe_eq_HaarRow (t : ℝ) (ht : 0 ≤ t) :
    ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 specialUnitaryTwoWilsonRankPositive t ht
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)) :
      Lp ℝ 2 haar) = L (F t) := by
  apply Lp.ext
  have h := p4Q2IV_originalFineWilsonPhysicalUnit_rawFiber_ae
    (halfExtent := fun _ => H) (beta := fun _ => t) (hbeta := fun _ => ht) 0
  exact h.trans ((F t).coeFn_toLp (p := 2) (𝕜 := ℝ) haar).symm

/-- Actual original GI gap of the genuine physical constant unit. -/
theorem p4Q2JI_originalGI_physicalUnit_eq (e : Link) (z : Cfg × Cfg) :
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H b hb
      (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2) e z =
        G e z (L (1 : C(Cfg, ℝ))) := by
  let U := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  have hU : (fun A : Cfg => (U : Lp ℝ 2 haar) A) =ᵐ[haar]
      (1 : C(Cfg, ℝ)) := by
    change (fun A : Cfg => (Lp.const 2 haar (1 : ℝ)) A) =ᵐ[haar] (fun _ => 1)
    exact Lp.coeFn_const (μ := haar) (p := 2) (c := (1 : ℝ))
  have hULp : (U : Lp ℝ 2 haar) = L (1 : C(Cfg, ℝ)) := by
    apply Lp.ext
    exact hU.trans ((1 : C(Cfg, ℝ)).coeFn_toLp (p := 2) (𝕜 := ℝ) haar).symm
  have h := p4Q2JH_originalGIResponseCLM_agrees_with_physicalGI
    H b hb e z U (1 : C(Cfg, ℝ)) hU
  rw [hULp] at h
  exact h.symm

/-- The true norm-normalized fine physical source contributes only the
nonzero inverse transfer norm to this fixed original GI detector. No
derivative of that norm is required for detecting a nonzero minor. -/
theorem p4Q2JI_originalGI_normalizedFineUnit_eq (t : ℝ) (ht : 0 ≤ t)
    (e : Link) (z : Cfg × Cfg) :
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H b hb
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        H 2 specialUnitaryTwoWilsonRankPositive t ht
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)) e z =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 specialUnitaryTwoWilsonRankPositive t ht‖⁻¹ * G e z (L (F t)) := by
  let U := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive t ht
  let V := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive t ht U
  let c : ℝ := ‖T‖⁻¹
  have hVLp : (V : Lp ℝ 2 haar) = c • L (F t) := by
    change c • ((T U) : Lp ℝ 2 haar) = c • L (F t)
    rw [p4Q2JI_actualRawFineUnit_coe_eq_HaarRow H t ht]
  have hV : (fun A : Cfg => (V : Lp ℝ 2 haar) A) =ᵐ[haar]
      (c • F t : C(Cfg, ℝ)) := by
    rw [hVLp]
    filter_upwards [Lp.coeFn_smul c (L (F t)),
      (F t).coeFn_toLp (p := 2) (𝕜 := ℝ) haar] with A hs hf
    rw [hs, Pi.smul_apply, hf]
    rfl
  have h := p4Q2JH_originalGIResponseCLM_agrees_with_physicalGI
    H b hb e z V (c • F t) hV
  rw [hVLp, map_smul, smul_eq_mul] at h
  exact h.symm

/-- The literal original GI two-context minor of the actual physical
constant/normalized-fine source pair. -/
noncomputable def p4Q2JI_originalPhysicalNormalizedMinor
    (e e' : Link) (z z' : Cfg × Cfg) (t : ℝ) (ht : 0 ≤ t) : ℝ :=
  let U := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let V := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive t ht U
  let gap := p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H b hb
  gap U e z * gap V e' z' - gap V e z * gap U e' z'

theorem p4Q2JI_originalPhysicalNormalizedMinor_eq_raw_scaled
    (e e' : Link) (z z' : Cfg × Cfg) (t : ℝ) (ht : 0 ≤ t) :
    p4Q2JI_originalPhysicalNormalizedMinor H b hb e e' z z' t ht =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 specialUnitaryTwoWilsonRankPositive t ht‖⁻¹ *
      p4Q2JI_originalGIRawFineRowMinor H b hb e e' z z' t := by
  dsimp only [p4Q2JI_originalPhysicalNormalizedMinor]
  rw [p4Q2JI_originalGI_physicalUnit_eq H b hb e z,
    p4Q2JI_originalGI_physicalUnit_eq H b hb e' z',
    p4Q2JI_originalGI_normalizedFineUnit_eq H b hb t ht e z,
    p4Q2JI_originalGI_normalizedFineUnit_eq H b hb t ht e' z']
  unfold p4Q2JI_originalGIRawFineRowMinor
  ring

/-- Conditional but genuinely physical conclusion: one NONZERO actual
spatial-Wilson determinant implies a nonzero original two-posterior GI
minor for the TRUE normalized fine source, throughout a positive window. -/
theorem p4Q2JI_originalPhysicalNormalizedMinor_smallPositive
    (e e' : Link) (z z' : Cfg × Cfg)
    (hW : p4Q2JI_originalGISpatialActionMinor H b hb e e' z z' ≠ 0) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ t : ℝ, ∀ ht : 0 < t, t < eps →
      p4Q2JI_originalPhysicalNormalizedMinor H b hb e e' z z' t ht.le ≠ 0 := by
  obtain ⟨eps, heps, hraw⟩ :=
    p4Q2JI_originalGIRawFineRowMinor_smallPositive_of_spatialMinor_ne H b hb e e' z z' hW
  refine ⟨eps, heps, ?_⟩
  intro t ht hsmall
  rw [p4Q2JI_originalPhysicalNormalizedMinor_eq_raw_scaled]
  exact mul_ne_zero
    (inv_ne_zero (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 specialUnitaryTwoWilsonRankPositive t ht.le).ne')
    (hraw t ht hsmall)

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JI_actualHaarL2Derivative_eq_spatialAction_and_constant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JI_originalGIRawFineRowMinor_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JI_originalGIRawFineRowMinor_hasDerivAt_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JI_originalGIRawFineRowMinor_smallPositive_of_spatialMinor_ne
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JI_actualRawFineUnit_coe_eq_HaarRow
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JI_originalGI_physicalUnit_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JI_originalGI_normalizedFineUnit_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JI_originalPhysicalNormalizedMinor_eq_raw_scaled
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JI_originalPhysicalNormalizedMinor_smallPositive
