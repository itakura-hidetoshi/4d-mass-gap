import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonThreePointSpatialMinorEquivalenceV5_PH
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalUnitWilsonHaarKernelSectionV5_IV
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-!
# P4-Q2-PI — exact UNNORMALIZED original Wilson two-slab spatial minor

PH makes true physical rank three equivalent (under independently proved
D2>0) to a nonzero determinant of three actual spatial values of the
normalized one- and two-slab genuine Wilson transfer.

For direct Wilson-kernel analysis we MUST remove the transfer operator
norm without differentiating it or substituting another measure.

Write W_t for the UNMODIFIED original physical Wilson one-slab
transfer, lambda_t=||W_t||>0, U for the Gauss-law constant unit.
Use OU's EXACT continuous synthesis of W_t U and W_t(W_t U):
  G1 = OU_t(U), G2 = OU_t(W_t U).
The latter is the complete TWO-STEP original Wilson transfer of the
original source, not an auxiliary independent-Haar Markov process.

Prove the OU synthesis is real-linear by its actual raw physical L2
operator equality and injective continuous-to-L2 embedding; prove
the exact pointwise original kernel row Haar integral for G1.

The normalized PF profiles satisfy POINTWISE:
  phi1 = lambda_t^(-1) G1
  phi2 = lambda_t^(-2) G2.
Hence the ORIGINAL three-spatial-point minor satisfies the exact
normalization identity
  M_normalized(A,B,C) = lambda_t^(-3) M_raw(A,B,C).
Since lambda_t>0, strict true D3 positivity is equivalent (when
D2>0) to a NONZERO raw original one/two-slab Wilson determinant.

This is the correct starting surface for the coupling-Taylor
construction of a literal nonzero configuration triple.
PI does NOT assert such a triple exists; no third-rank assumption,
invented spectral measure, independent-Haar posterior, Dobrushin,
sorry/admit, new axiom, U0 or continuum mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Matrix
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PI_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PI_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PI_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PI_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PI_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance p4Q2PI_specialUnitaryNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun V : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (V : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

local instance p4Q2PI_specialUnitaryHaarOpenPos :
    Measure.IsOpenPosMeasure
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  dsimp [normalizedCompactHaar]
  infer_instance

local instance p4Q2PI_spatialFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance p4Q2PI_spatialProductHaarOpenPos (H : ℕ) :
    Measure.IsOpenPosMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint

section ActualOriginalRawTwoSlab
variable (H : ℕ) (t : ℝ) (ht : 0 ≤ t)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "U" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
local notation "Raw" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive t ht
local notation "Fine" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive t ht
local notation "D2" => p4Q2PD_originalWilsonTwoMomentDet H t ht
local notation "D3" => p4Q2PD_originalWilsonThirdMomentGap H t ht
local notation "F1" =>
  p4Q2PF_originalWilsonOneSlabContinuous H t ht
local notation "F2" =>
  p4Q2PF_originalWilsonTwoSlabContinuous H t ht
local notation "L" => ContinuousMap.toLp 2 haar ℝ

/-- Canonical feature synthesis of the UNNORMALIZED original Wilson
one-slab transfer acting on the authentic physical constant. -/
noncomputable def p4Q2PI_originalRawOneSlabContinuous : C(Cfg, ℝ) :=
  p4Q2OU_originalPhysicalTransferContinuous H t ht U

/-- Canonical feature synthesis of TWO successive applications of
the SAME original UNNORMALIZED Wilson physical operator W_t. -/
noncomputable def p4Q2PI_originalRawTwoSlabContinuous : C(Cfg, ℝ) :=
  p4Q2OU_originalPhysicalTransferContinuous H t ht (Raw U)

/-- Real scalar linearity of the ORIGINAL continuous Wilson synthesis.
Proved from the genuine Gauss-law raw operator and Haar L2 full support,
without postulating a new kernel-linear action. -/
theorem p4Q2PI_originalRawContinuous_smul
    (c : ℝ) (f : Phys) :
    p4Q2OU_originalPhysicalTransferContinuous H t ht (c • f) =
      c • p4Q2OU_originalPhysicalTransferContinuous H t ht f := by
  apply (ContinuousMap.toLp_injective
    (𝕜 := ℝ) (p := (2 : ℝ≥0∞)) (μ := haar))
  have hRawSmul : Raw (c • f) = c • Raw f := by
    exact map_smul Raw c f
  have hCoerce :
      ((Raw (c • f) : Phys) : Lp ℝ 2 haar) =
        c • ((Raw f : Phys) : Lp ℝ 2 haar) := by
    rw [hRawSmul]
    rfl
  calc
    L (p4Q2OU_originalPhysicalTransferContinuous H t ht (c • f)) =
        ((Raw (c • f) : Phys) : Lp ℝ 2 haar) :=
      (p4Q2OU_originalPhysicalTransferContinuous_toLp H t ht (c • f)).symm
    _ = c • ((Raw f : Phys) : Lp ℝ 2 haar) := hCoerce
    _ = c • L (p4Q2OU_originalPhysicalTransferContinuous H t ht f) := by
          rw [p4Q2OU_originalPhysicalTransferContinuous_toLp H t ht f]
    _ = L (c • p4Q2OU_originalPhysicalTransferContinuous H t ht f) := by
          rw [map_smul]

/-- The unnormalized Wilson one-slab continuous OU representative
agrees POINTWISE with the LITERAL original spatial Haar kernel row
integral, not just almost everywhere in L2. -/
theorem p4Q2PI_originalRawOneSlab_eq_literalWilsonHaarRow
    (B : Cfg) :
    p4Q2PI_originalRawOneSlabContinuous H t ht B =
      p4Q2IV_originalWilsonUnitHaarKernelSection H t B := by
  let ψ : C(Cfg, ℝ) := p4Q2PI_originalRawOneSlabContinuous H t ht
  have hRep :
      (fun X : Cfg => ((Raw U : Phys) : Lp ℝ 2 haar) X) =ᵐ[haar] ψ := by
    rw [p4Q2OU_originalPhysicalTransferContinuous_toLp H t ht U]
    exact ψ.coeFn_toLp (p := 2) (𝕜 := ℝ) haar
  have hKernel :
      (fun X : Cfg => ((Raw U : Phys) : Lp ℝ 2 haar) X) =ᵐ[haar]
        p4Q2IV_originalWilsonUnitHaarKernelSection H t := by
    simpa using
      (p4Q2IV_originalFineWilsonPhysicalUnit_rawFiber_ae
        (halfExtent := fun _ => H) (beta := fun _ => t)
        (hbeta := fun _ => ht) 0)
  have hPointwise :
      (ψ : Cfg → ℝ) = p4Q2IV_originalWilsonUnitHaarKernelSection H t :=
    MeasureTheory.Measure.eq_of_ae_eq
      (hRep.symm.trans hKernel) ψ.continuous
      (p4Q2IV_originalWilsonUnitHaarKernelSection_continuous H t)
  exact congrFun hPointwise B

/-- The normalized original TWO-step PF continuous representative is
exactly the unnormalized TWO-step continuous Wilson synthesis scaled
by the SQUARE of the original raw transfer norm. -/
theorem p4Q2PI_originalNormalizedTwoSlab_eq_rawSquare :
    F2 = (‖Raw‖⁻¹) ^ 2 •
      p4Q2PI_originalRawTwoSlabContinuous H t ht := by
  let v : ℝ := ‖Raw‖⁻¹
  have hFine : Fine U = v • Raw U := by
    simpa only [v] using
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_apply
        H 2 specialUnitaryTwoWilsonRankPositive t ht U)
  calc
    F2 = v • p4Q2OU_originalPhysicalTransferContinuous H t ht (Fine U) := by
      rfl
    _ = v • p4Q2OU_originalPhysicalTransferContinuous H t ht (v • Raw U) := by
      rw [hFine]
    _ = v • (v • p4Q2OU_originalPhysicalTransferContinuous H t ht (Raw U)) := by
      rw [p4Q2PI_originalRawContinuous_smul H t ht v (Raw U)]
    _ = (‖Raw‖⁻¹) ^ 2 • p4Q2PI_originalRawTwoSlabContinuous H t ht := by
      dsimp only [p4Q2PI_originalRawTwoSlabContinuous]
      rw [smul_smul]
      change (v * v) • _ = (v ^ 2) • _
      rw [pow_two]

/-- Three-configuration determinant of the TRUE unnormalized original
Wilson one-slab/two-slab physical continuous boundary functions. -/
noncomputable def p4Q2PI_originalRawThreeSpatialPointMinor
    (A B C : Cfg) : ℝ :=
  (p4Q2PI_originalRawOneSlabContinuous H t ht B -
      p4Q2PI_originalRawOneSlabContinuous H t ht A) *
    (p4Q2PI_originalRawTwoSlabContinuous H t ht C -
      p4Q2PI_originalRawTwoSlabContinuous H t ht A) -
  (p4Q2PI_originalRawOneSlabContinuous H t ht C -
      p4Q2PI_originalRawOneSlabContinuous H t ht A) *
    (p4Q2PI_originalRawTwoSlabContinuous H t ht B -
      p4Q2PI_originalRawTwoSlabContinuous H t ht A)

/-- Exact original Wilson normalization scaling of the entire spatial
3x3 evaluation determinant. No division by fine coupling and NO
derivative of the Perron/transfer normalization occurs. -/
theorem p4Q2PI_normalizedThreeSpatialMinor_eq_rawScaled
    (A B C : Cfg) :
    p4Q2PG_originalWilsonThreeSpatialPointMinor H t ht A B C =
      (‖Raw‖⁻¹) ^ 3 *
        p4Q2PI_originalRawThreeSpatialPointMinor H t ht A B C := by
  let v : ℝ := ‖Raw‖⁻¹
  have hOne (X : Cfg) :
      F1 X = v * p4Q2PI_originalRawOneSlabContinuous H t ht X := by
    rfl
  have hTwo (X : Cfg) :
      F2 X = v ^ 2 * p4Q2PI_originalRawTwoSlabContinuous H t ht X := by
    rw [p4Q2PI_originalNormalizedTwoSlab_eq_rawSquare H t ht]
    simp only [ContinuousMap.smul_apply, smul_eq_mul]
  unfold p4Q2PG_originalWilsonThreeSpatialPointMinor
    p4Q2PI_originalRawThreeSpatialPointMinor
  rw [hOne A, hOne B, hOne C, hTwo A, hTwo B, hTwo C]
  change _ = (v ^ 3) * _
  ring

/-- Since the actual Wilson raw transfer has STRICTLY POSITIVE
operator norm, its third-power inverse normalization cannot cause
nor erase a genuine nonzero three-configuration spatial minor. -/
theorem p4Q2PI_normalizedThreeSpatialMinor_ne_iff_raw
    (A B C : Cfg) :
    p4Q2PG_originalWilsonThreeSpatialPointMinor H t ht A B C ≠ 0 ↔
      p4Q2PI_originalRawThreeSpatialPointMinor H t ht A B C ≠ 0 := by
  have hnorm : 0 < ‖Raw‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 specialUnitaryTwoWilsonRankPositive t ht
  have hv : (‖Raw‖⁻¹) ^ 3 ≠ 0 :=
    pow_ne_zero _ (inv_ne_zero hnorm.ne')
  rw [p4Q2PI_normalizedThreeSpatialMinor_eq_rawScaled]
  constructor
  · intro h
    intro hraw
    apply h
    rw [hraw, mul_zero]
  · intro hraw
    exact mul_ne_zero hv hraw

/-- Original TRUE physical 3x3 Hankel positivity iff some three
ACTUAL spatial boundaries have nonzero TWO-ITERATION UNNORMALIZED
Wilson determinant, under the already-proved 2x2 physical pivot.
This removes the unknown raw operator norm entirely from the
forthcoming small-fine original kernel expansion. -/
theorem p4Q2PI_originalThirdMoment_pos_iff_exists_rawSpatialMinor
    (hTwo : 0 < D2) :
    0 < D3 ↔
      ∃ A B C : Cfg,
        p4Q2PI_originalRawThreeSpatialPointMinor H t ht A B C ≠ 0 := by
  rw [p4Q2PH_originalThirdMoment_pos_iff_exists_threeSpatialMinor H t ht hTwo]
  constructor
  · rintro ⟨A, B, C, hNorm⟩
    exact ⟨A, B, C,
      (p4Q2PI_normalizedThreeSpatialMinor_ne_iff_raw H t ht A B C).mp hNorm⟩
  · rintro ⟨A, B, C, hRaw⟩
    exact ⟨A, B, C,
      (p4Q2PI_normalizedThreeSpatialMinor_ne_iff_raw H t ht A B C).mpr hRaw⟩

end ActualOriginalRawTwoSlab

section ActualSmallFineRawMinor
variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n : ℕ)
local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn

/-- The original frozen-positive two-interacting posterior's valid
small-positive-fine D2 interval also yields a FULL iff for raw
two-iteration Wilson spatial minors and genuine physical D3>0.
A nonzero configuration triple is not postulated or constructed. -/
theorem p4Q2PI_actualSmallFine_thirdMoment_pos_iff_exists_rawSpatialMinor
    (hFrozen : 0 < beta n) (e e' : Link)
    (left₀ right₀ : Cfg) :
    ∃ delta : ℝ, 0 < delta ∧
      (0 < beta (n + 1) → beta (n + 1) < delta →
        (0 < p4Q2PD_originalWilsonThirdMomentGap
            Hn (beta (n + 1)) (hbeta (n + 1)) ↔
          ∃ A B C : Cfg,
            p4Q2PI_originalRawThreeSpatialPointMinor
              Hn (beta (n + 1)) (hbeta (n + 1)) A B C ≠ 0)) := by
  obtain ⟨delta, hdelta, hTwo⟩ :=
    p4Q2PE_actualSmallFine_trueMomentPivot_pos
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e e' left₀ right₀
  refine ⟨delta, hdelta, ?_⟩
  intro ht hsmall
  exact p4Q2PI_originalThirdMoment_pos_iff_exists_rawSpatialMinor
    Hn (beta (n + 1)) (hbeta (n + 1)) (hTwo ht hsmall)

end ActualSmallFineRawMinor

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PI_originalRawContinuous_smul
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PI_originalRawOneSlab_eq_literalWilsonHaarRow
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PI_originalNormalizedTwoSlab_eq_rawSquare
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PI_normalizedThreeSpatialMinor_eq_rawScaled
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PI_normalizedThreeSpatialMinor_ne_iff_raw
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PI_originalThirdMoment_pos_iff_exists_rawSpatialMinor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PI_actualSmallFine_thirdMoment_pos_iff_exists_rawSpatialMinor
