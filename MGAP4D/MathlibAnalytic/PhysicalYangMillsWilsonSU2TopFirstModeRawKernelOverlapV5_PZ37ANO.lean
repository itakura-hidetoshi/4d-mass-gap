import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2PhysicalTwoModeVacuumOverlapObstructionV5_PZ37ANM
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabTransferRawIntegral
import MGAP4D.MathlibAnalytic.RealL2HilbertSchmidtSeparableKernelOperator
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ANO — original physical Wilson top/first-mode kernel overlap

The overlap of the true nonnegative top physical Gauss-law eigenvector with the
first native Wilson Gram--Schmidt mode is exposed through the literal two-boundary
original one-slab Wilson Haar kernel, with no change to model or top space.

At beta zero the kernel is the constant-one kernel. The corresponding exact
rank-one Haar factorization and the true first-mode orthogonality force
the physical overlap to vanish. At positive beta the exact integral coefficient
remains a separately open sign/nonvanishing problem.

No physical/OS Hilbert identification, OS nonzero class, or continuum mass gap
is asserted.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

local instance p4Q2PZ37ANO_group :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ANO_compact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ANO_countable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ANO_measurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ANO_borel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance p4Q2PZ37ANO_spatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance p4Q2PZ37ANO_spatialHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  infer_instance

/-- The unchanged literal original SU(2) one-slab Wilson kernel is identically
one at beta zero, for every finite spatial scale, with both endpoint
halfweights and the temporal crossing factor retained in the definition. -/
theorem p4Q2PZ37ANO_originalOneSlabKernel_betaZero
    (H : ℕ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 0 A B = 1 := by
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann]
  simp

/-- The top/first-mode overlap multiplied by the actual positive physical
one-slab top eigenvalue is EXACTLY the native two-boundary Wilson-kernel
Haar integral. This is an explicit model coefficient, not a hypothesis
about an unrelated OS boundary observable. -/
theorem p4Q2PZ37ANO_originalTopModeOne_overlap_mul_norm_eq_rawKernel
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) beta hbeta‖ *
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H 2 (by norm_num) beta hbeta)
        (p4Q2PZ37AMU_actualPhysicalGaussMode H 1) =
    ∫ p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H 2 beta p.1 p.2 *
        (((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
            H 2 (by norm_num) beta hbeta :
              PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2) :
                Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2))
              p.1 *
          ((p4Q2PZ37AMU_actualPhysicalGaussMode H 1 :
              PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2) :
                Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2))
              p.2)
      ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2) := by
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) beta hbeta
  let Ω := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
    H 2 (by norm_num) beta hbeta
  let v1 := p4Q2PZ37AMU_actualPhysicalGaussMode H 1
  have heigen : T Ω = ‖T‖ • Ω :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_eigen
      H 2 (by norm_num) beta hbeta
  have hraw :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_inner_eq_rawIntegral
      H 2 (by norm_num) beta hbeta Ω v1
  calc
    ‖T‖ * inner ℝ Ω v1 = inner ℝ (T Ω) v1 := by
      rw [heigen]
      exact (real_inner_smul_left Ω v1 ‖T‖).symm
    _ = _ := hraw

/-- At beta zero the ACTUAL product-Haar L² kernel is the external tensor
of the two constant-one Haar vectors; no proxy rank-one operator is used. -/
theorem p4Q2PZ37ANO_originalOneSlabPairKernel_betaZero_eq_oneTensor
    (H : ℕ) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
        H 2 (by norm_num) 0 (by norm_num) =
      realL2ExternalTensor
        (Lp.const 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) (1 : ℝ))
        (Lp.const 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) (1 : ℝ)) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let c : Lp ℝ 2 μ := Lp.const 2 μ (1 : ℝ)
  have hc : c =ᵐ[μ] (fun _ => (1 : ℝ)) := by
    simpa only [c, Function.const_apply] using
      (Lp.coeFn_const (μ := μ) (p := (2 : ℝ≥0∞)) (c := (1 : ℝ)))
  have hf :
      (fun p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 => c p.1)
        =ᵐ[μ.prod μ] (fun _ => (1 : ℝ)) := by
    simpa [Function.comp_def] using
      (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae_eq hc
  have hg :
      (fun p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 => c p.2)
        =ᵐ[μ.prod μ] (fun _ => (1 : ℝ)) := by
    simpa [Function.comp_def] using
      (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae_eq hc
  apply Lp.ext
  have hk :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2_coeFn
      H 2 (by norm_num) 0 (by norm_num)
  have ht := realL2ExternalTensor_coeFn c c
  filter_upwards [hk, ht, hf, hg] with p hkp htp hcp hgp
  rw [hkp]
  change
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
      H 2 0 p.1 p.2 = (realL2ExternalTensor c c) p
  rw [htp]
  change
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
      H 2 0 p.1 p.2 = c p.1 * c p.2
  rw [p4Q2PZ37ANO_originalOneSlabKernel_betaZero H p.1 p.2, hcp, hgp]
  ring

/-- The TRUE original nonnegative Wilson physical vacuum has exactly zero
overlap with the native first excited Gram--Schmidt mode at beta zero.
In particular ANM's nonzero-c0 criterion does not hold at beta zero. -/
theorem p4Q2PZ37ANO_originalPhysicalTopModeOne_overlap_betaZero_eq_zero
    (H : ℕ) :
    inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
        H 2 (by norm_num) 0 (by norm_num))
      (p4Q2PZ37AMU_actualPhysicalGaussMode H 1) = 0 := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let c : Lp ℝ 2 μ := Lp.const 2 μ (1 : ℝ)
  let Ω : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
      H 2 (by norm_num) 0 (by norm_num)
  let v1 : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2 :=
    p4Q2PZ37AMU_actualPhysicalGaussMode H 1
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) 0 (by norm_num)
  have ho := p4Q2PZ37AMU_actualPhysicalGaussMode_orthonormal H
  have h01 :
      inner ℝ (p4Q2PZ37AMU_actualPhysicalGaussMode H 0)
        (p4Q2PZ37AMU_actualPhysicalGaussMode H 1) = 0 :=
    ho.inner_eq_zero (by decide : (0 : ℕ) ≠ 1)
  rw [p4Q2PZ37ANM_actualModeZero_eq_physicalConstant] at h01
  have hmode1 : inner ℝ c (v1 : Lp ℝ 2 μ) = 0 := h01
  have hraw :
      inner ℝ (T Ω) v1 =
        realL2HilbertSchmidtKernelPairing
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
            H 2 (by norm_num) 0 (by norm_num))
          (Ω : Lp ℝ 2 μ) (v1 : Lp ℝ 2 μ) := by
    change
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H 2 (by norm_num) 0 (by norm_num) (Ω : Lp ℝ 2 μ))
        (v1 : Lp ℝ 2 μ) = _
    exact periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_inner
      H 2 (by norm_num) 0 (by norm_num) Ω v1
  have hTzero : inner ℝ (T Ω) v1 = 0 := by
    calc
      inner ℝ (T Ω) v1 =
          realL2HilbertSchmidtKernelPairing
            (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
              H 2 (by norm_num) 0 (by norm_num))
            (Ω : Lp ℝ 2 μ) (v1 : Lp ℝ 2 μ) := hraw
      _ = inner ℝ c (Ω : Lp ℝ 2 μ) *
          inner ℝ c (v1 : Lp ℝ 2 μ) := by
            rw [p4Q2PZ37ANO_originalOneSlabPairKernel_betaZero_eq_oneTensor]
            exact realL2HilbertSchmidtKernelPairing_externalTensor
              c (Ω : Lp ℝ 2 μ) c (v1 : Lp ℝ 2 μ)
      _ = 0 := by rw [hmode1, mul_zero]
  have heigen : T Ω = ‖T‖ • Ω :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_eigen
      H 2 (by norm_num) 0 (by norm_num)
  have hpos : 0 < ‖T‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 (by norm_num) 0 (by norm_num)
  have hmul : ‖T‖ * inner ℝ Ω v1 = 0 := by
    calc
      ‖T‖ * inner ℝ Ω v1 = inner ℝ (T Ω) v1 := by
        rw [heigen]
        exact (real_inner_smul_left Ω v1 ‖T‖).symm
      _ = 0 := hTzero
  exact (mul_eq_zero.mp hmul).resolve_left (ne_of_gt hpos)

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANO_originalOneSlabKernel_betaZero
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANO_originalTopModeOne_overlap_mul_norm_eq_rawKernel
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANO_originalOneSlabPairKernel_betaZero_eq_oneTensor
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANO_originalPhysicalTopModeOne_overlap_betaZero_eq_zero
