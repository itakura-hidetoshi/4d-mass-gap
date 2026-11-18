import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2RawFirstVariationResponseV5_PZ37ANS
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabPairObservableInsertion
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ANT — true Wilson first Haar moment and quadratic fixed-response error

The actual original SU(2) one-slab action S_H(A,B), with both spatial
halfweights and temporal crossing terms, is realized in the genuine
pair-Haar L² space. ANS already machine-verified pointwise
|K_beta - 1 + beta*S| <= (C_H beta)^2 for 0<=C_H beta<=1.

Here this actual-model estimate is transported into a product-Haar
L² kernel norm bound, and then paired with the actual physical
constant-one Gauss-law input and the native first Wilson-energy
Gram--Schmidt output mode.

Thus the original fixed-Haar response is equal to
  - beta * (original pair-Haar Wilson-action first moment)
up to a certified O(beta²) remainder. The action-insertion moment
remains a concrete original-model integral, whose exact value
and sign require separate computation.

Neither the Wilson kernel nor its Haar measure or physical carrier
is modified. No unconditional positive-beta overlap or continuum
Yang--Mills mass gap is claimed.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

local instance p4Q2PZ37ANT_group :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ANT_compact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ANT_countable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ANT_measurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ANT_borel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ANT_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance p4Q2PZ37ANT_pairHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2) := by
  infer_instance
local instance p4Q2PZ37ANT_sliceHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  infer_instance

/-- The unchanged true finite-volume symmetric SU(2) one-slab action is
a pair-Haar square-integrable scalar function. This includes BOTH spatial
halfweights and the original temporal crossing terms. -/
theorem p4Q2PZ37ANT_originalSlabAction_pairHaar_memLp_two (H : ℕ) :
    MemLp
      (fun p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction
          H 2 p.1 p.2)
      2 (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
  let C := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  let S := fun p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 =>
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2 p.1 p.2
  have hW := periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H 2
  have hcross := periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction_continuous H 2
  have hcont : Continuous S := by
    dsimp [S, periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction]
    exact
      ((continuous_const.mul (hW.comp continuous_fst)).add hcross).add
        (continuous_const.mul (hW.comp continuous_snd))
  have hmeas : AEStronglyMeasurable S μ :=
    hcont.measurable.aestronglyMeasurable
  have hbound : ∀ p, ‖S p‖ ≤ C := by
    intro p
    have hlow :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_nonneg
        H 2 (by norm_num) p.1 p.2
    have hup :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_le_globalBudget
        H 2 (by norm_num) p.1 p.2
    simpa [S, C, Real.norm_eq_abs, abs_of_nonneg hlow] using hup
  have hTop : MemLp S ⊤ μ :=
    memLp_top_of_bound hmeas C (Filter.Eventually.of_forall hbound)
  exact hTop.mono_exponent (by norm_num)

/-- A vector in the ORIGINAL product-Haar L² space representing the full
literal Wilson one-slab action, not a proxy or changed physics. -/
noncomputable def p4Q2PZ37ANT_originalSlabAction_pairHaarL2
    (H : ℕ) :
    Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2) :=
  (p4Q2PZ37ANT_originalSlabAction_pairHaar_memLp_two H).toLp
    (fun p => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction
      H 2 p.1 p.2)

/-- The actual Wilson action L² class retains the literal measurable action
as its pair-Haar a.e. representative. -/
theorem p4Q2PZ37ANT_originalSlabAction_pairHaarL2_coeFn
    (H : ℕ) :
    p4Q2PZ37ANT_originalSlabAction_pairHaarL2 H
      =ᵐ[periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2]
      (fun p => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction
        H 2 p.1 p.2) :=
  (p4Q2PZ37ANT_originalSlabAction_pairHaar_memLp_two H).coeFn_toLp

/-- True original Wilson kernel L² first-order expansion, bounded in
the NATIVE pair-Haar norm. In particular, this promotes ANS's pointwise
Taylor estimate without identifying the physical Wilson carrier with
an OS completion or assuming beta analyticity of top eigenvectors. -/
theorem p4Q2PZ37ANT_originalKernel_pairHaarL2_firstVariation_norm_le
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (hsmall :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        beta ≤ 1) :
    ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
        H 2 (by norm_num) beta hbeta -
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
        H 2 (by norm_num) 0 (by norm_num) +
      beta • p4Q2PZ37ANT_originalSlabAction_pairHaarL2 H‖ ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        beta)^2 := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
  let C := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  let K := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
    H 2 (by norm_num) beta hbeta
  let K0 := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
    H 2 (by norm_num) 0 (by norm_num)
  let S := p4Q2PZ37ANT_originalSlabAction_pairHaarL2 H
  let Q : Lp ℝ 2 μ := K - K0 + beta • S
  let B : Lp ℝ 2 μ := Lp.const 2 μ ((C * beta)^2)
  have hK := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2_coeFn
    H 2 (by norm_num) beta hbeta
  have hK0 := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2_coeFn
    H 2 (by norm_num) 0 (by norm_num)
  have hS := p4Q2PZ37ANT_originalSlabAction_pairHaarL2_coeFn H
  have hQadd := Lp.coeFn_add (K - K0) (beta • S)
  have hQsub := Lp.coeFn_sub K K0
  have hQsmul := Lp.coeFn_smul beta S
  have hB := Lp.coeFn_const (μ := μ) (p := (2 : ENNReal)) (c := ((C * beta)^2))
  have hle : ∀ᵐ p ∂μ, ‖Q p‖ ≤ ‖B p‖ := by
    filter_upwards [hQadd, hQsub, hQsmul, hK, hK0, hS, hB] with
      p ha hs hsm hk hk0 hSval hBval
    simp only [Q, B, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] at *
    rw [ha, hs, hsm, hk, hk0, hSval, hBval]
    have hTaylor :=
      p4Q2PZ37ANS_originalOneSlabKernel_quadraticRemainder
        H beta hbeta hsmall p.1 p.2
    simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (C * beta)),
      C, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hTaylor
  have hnorm : ‖Q‖ ≤ ‖B‖ := Lp.norm_le_norm_of_ae_le hle
  have hnormB : ‖B‖ = (C * beta)^2 := by
    change ‖Lp.const 2 μ ((C * beta)^2)‖ = _
    have h :=
      Lp.norm_const' (μ := μ) (p := (2 : ENNReal))
        (c := ((C * beta)^2)) (by norm_num) (by norm_num)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (C * beta))] using h
  change ‖Q‖ ≤ (C * beta)^2
  exact hnorm.trans_eq hnormB

/-- The true finite-volume original one-slab physical fixed-Haar response
has first-order coefficient the literal SU(2) pair-Haar Wilson-action
insertion moment; its remainder is O_H(beta²), with explicit C_H.
No sign of that actual first moment is asserted here. -/
theorem p4Q2PZ37ANT_originalFixedHaarResponse_firstMoment_quadratic
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (hsmall :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        beta ≤ 1) :
    |inner ℝ
        ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H 2 (by norm_num) beta hbeta -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H 2 (by norm_num) 0 (by norm_num))
          (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2))
        (p4Q2PZ37AMU_actualPhysicalGaussMode H 1) +
      beta * inner ℝ
        (p4Q2PZ37ANT_originalSlabAction_pairHaarL2 H)
        (realL2ExternalTensor
          ((periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2 :
              PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2) :
              Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2))
          ((p4Q2PZ37AMU_actualPhysicalGaussMode H 1 :
              PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2) :
              Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)))| ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        beta)^2 := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let K := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
    H 2 (by norm_num) beta hbeta
  let K0 := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
    H 2 (by norm_num) 0 (by norm_num)
  let S := p4Q2PZ37ANT_originalSlabAction_pairHaarL2 H
  let c : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let v1 := p4Q2PZ37AMU_actualPhysicalGaussMode H 1
  let E : Lp ℝ 2 (μ.prod μ) :=
    realL2ExternalTensor (c : Lp ℝ 2 μ) (v1 : Lp ℝ 2 μ)
  let Q := K - K0 + beta • S
  let C := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  have hc : ‖c‖ = 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_norm H 2
  have hv1 : ‖v1‖ = 1 :=
    (p4Q2PZ37AMU_actualPhysicalGaussMode_orthonormal H).1 1
  have hE : ‖E‖ = 1 := by
    dsimp [E]
    rw [realL2ExternalTensor_norm]
    change ‖c‖ * ‖v1‖ = 1
    rw [hc, hv1, one_mul]
  have hT :
      inner ℝ K E =
        inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H 2 (by norm_num) beta hbeta c) v1 := by
    change
      realL2HilbertSchmidtKernelPairing K (c : Lp ℝ 2 μ)
          (v1 : Lp ℝ 2 μ) =
        inner ℝ
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
            H 2 (by norm_num) beta hbeta (c : Lp ℝ 2 μ))
          (v1 : Lp ℝ 2 μ)
    exact (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_inner
      H 2 (by norm_num) beta hbeta (c : Lp ℝ 2 μ) (v1 : Lp ℝ 2 μ)).symm
  have hT0 :
      inner ℝ K0 E =
        inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H 2 (by norm_num) 0 (by norm_num) c) v1 := by
    change
      realL2HilbertSchmidtKernelPairing K0 (c : Lp ℝ 2 μ)
          (v1 : Lp ℝ 2 μ) =
        inner ℝ
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
            H 2 (by norm_num) 0 (by norm_num) (c : Lp ℝ 2 μ))
          (v1 : Lp ℝ 2 μ)
    exact (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_inner
      H 2 (by norm_num) 0 (by norm_num) (c : Lp ℝ 2 μ) (v1 : Lp ℝ 2 μ)).symm
  have hinner :
      inner ℝ Q E =
        inner ℝ
          ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
              H 2 (by norm_num) beta hbeta -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
              H 2 (by norm_num) 0 (by norm_num)) c) v1 +
        beta * inner ℝ S E := by
    dsimp [Q]
    rw [inner_add_left, inner_sub_left, real_inner_smul_left, hT, hT0]
    rw [ContinuousLinearMap.sub_apply, inner_sub_left]
  have hnorm :
      ‖Q‖ ≤ (C * beta)^2 :=
    p4Q2PZ37ANT_originalKernel_pairHaarL2_firstVariation_norm_le
      H beta hbeta hsmall
  have hcs : |inner ℝ Q E| ≤ ‖Q‖ * ‖E‖ :=
    abs_real_inner_le_norm Q E
  calc
    |inner ℝ
        ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H 2 (by norm_num) beta hbeta -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H 2 (by norm_num) 0 (by norm_num)) c) v1 +
        beta * inner ℝ S E| =
      |inner ℝ Q E| := congrArg abs hinner.symm
    _ ≤ ‖Q‖ * ‖E‖ := hcs
    _ = ‖Q‖ := by rw [hE, mul_one]
    _ ≤ (C * beta)^2 := hnorm

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANT_originalSlabAction_pairHaar_memLp_two
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANT_originalSlabAction_pairHaarL2
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANT_originalSlabAction_pairHaarL2_coeFn
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANT_originalKernel_pairHaarL2_firstVariation_norm_le
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANT_originalFixedHaarResponse_firstMoment_quadratic
