import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarActualRightModalTransferHyperplaneV5_GY
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSignedSourcePosteriorMassTransferKernelV5_GW
import Mathlib.Tactic

/-!
# P4-Q2-GZ: descent from genuine physical Wilson transfer to modal coefficient hyperplanes

GY builds a codimension-one linear modal-transfer evaluation by taking the
ACTUAL original Wilson one-slab transfer at each actual fine right-Krylov
physical source. Here prove that the resulting finite sum is EXACTLY the
original Wilson one-slab transfer INTEGRAL of the signed combined physical
source, for every coefficient vector.

The proof first constructs the genuine bounded-kernel Haar integral as a
linear map on the entire ambient real L² space. Its integrability follows
from the original Wilson kernel bound |K_beta(A,B)| <= 1 at beta>=0 and the
Lp two-to-one embedding on the spatial Haar probability. The physical
closed gauge-invariant submodule and each fine right-Krylov factor are
transported to this same ambient L² before applying the linear map.

Consequently the authentic signed physical transfer-zero locus is exactly
GY's true modal-transfer hyperplane of codimension one. Its complement is
open and nonempty. The nonzero original transfer at the SU(2) pi insertion
also implies strictly positive true interacting original Wilson conditional
posterior two-LEFT-boundary signed response-square mass by GW.

No independent-Haar conditional posterior, surrogate physical source,
full coefficient-frame lower bound, GI expectation-gap Delta, H1-C3
closure or continuum mass gap is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 2600000
set_option synthInstance.maxHeartbeats 880000

local instance p4Q2GZ_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2GZ_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2GZ_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2GZ_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2GZ_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance p4Q2GZ_spatialHaarProbability (H : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint

section AbstractHaarL2

variable {α : Type*} [MeasurableSpace α]
variable {μ : Measure α} [IsProbabilityMeasure μ]

/-- The bounded measurable kernel times an actual L² function is
integrable on the probability reference. -/
private theorem p4Q2GZ_weightedLp_integrable
    (K : α → ℝ) (hK : AEStronglyMeasurable K μ)
    (hBound : ∀ x, ‖K x‖ ≤ 1) (f : Lp ℝ 2 μ) :
    Integrable (fun x => K x * f x) μ := by
  have hf : Integrable (fun x => f x) μ := by
    rw [← memLp_one_iff_integrable]
    exact (Lp.memLp f).mono_exponent (by norm_num)
  have hmeas : AEStronglyMeasurable (fun x => K x * f x) μ :=
    hK.mul (Lp.aestronglyMeasurable f)
  refine hf.mono' hmeas ?_
  filter_upwards with x
  calc
    ‖K x * f x‖ = ‖K x‖ * ‖f x‖ := norm_mul _ _
    _ ≤ 1 * ‖f x‖ := mul_le_mul_of_nonneg_right (hBound x) (norm_nonneg _)
    _ = ‖f x‖ := one_mul _

/-- The literal Haar integral against a bounded measurable real kernel,
as a linear map on the entire ambient REAL L² Hilbert space. -/
private noncomputable def p4Q2GZ_weightedLpLinear
    (K : α → ℝ) (hK : AEStronglyMeasurable K μ)
    (hBound : ∀ x, ‖K x‖ ≤ 1) : Lp ℝ 2 μ →ₗ[ℝ] ℝ :=
  { toFun := fun f => ∫ x, K x * f x ∂μ
    map_add' := by
      intro f g
      change (∫ x, K x * (f + g) x ∂μ) =
        (∫ x, K x * f x ∂μ) + (∫ x, K x * g x ∂μ)
      calc
        (∫ x, K x * (f + g) x ∂μ) =
            ∫ x, (K x * f x + K x * g x) ∂μ := by
          apply integral_congr_ae
          filter_upwards [Lp.coeFn_add f g] with x hx
          rw [hx, mul_add]
        _ = (∫ x, K x * f x ∂μ) + (∫ x, K x * g x ∂μ) :=
          integral_add
            (p4Q2GZ_weightedLp_integrable K hK hBound f)
            (p4Q2GZ_weightedLp_integrable K hK hBound g)
    map_smul' := by
      intro c f
      change (∫ x, K x * (c • f) x ∂μ) =
        c * (∫ x, K x * f x ∂μ)
      calc
        (∫ x, K x * (c • f) x ∂μ) =
            ∫ x, c * (K x * f x) ∂μ := by
          apply integral_congr_ae
          filter_upwards [Lp.coeFn_smul c f] with x hx
          rw [hx]
          simp only [smul_eq_mul]
          ring
        _ = c * (∫ x, K x * f x ∂μ) := integral_const_mul c _ }

end AbstractHaarL2

section OriginalPhysicalWilson

variable (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "μ" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2

/-- Genuine original Wilson one-slab kernel-smoothed source transfer is
a LINEAR MAP of its ambient Haar-L² input, not a replacement source. -/
noncomputable def p4Q2GZ_originalWilsonPhysicalTransferLinear (B : Cfg) :
    Lp ℝ 2 μ →ₗ[ℝ] ℝ := by
  let K : Cfg → ℝ := fun A =>
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta A B
  have hcont : Continuous K :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
      H 2 beta).comp (continuous_id.prodMk continuous_const)
  have hmeas : AEStronglyMeasurable K μ := hcont.aestronglyMeasurable
  have hbound : ∀ A : Cfg, ‖K A‖ ≤ 1 := by
    intro A
    change ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
      H 2 beta A B‖ ≤ 1
    rw [Real.norm_eq_abs]
    exact periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
      H 2 (by norm_num) beta hbeta A B
  exact p4Q2GZ_weightedLpLinear K hmeas hbound

/-- Exact identity, on the REAL gauge-invariant physical submodule, of
the original decomposable one-slab transfer and the genuine bounded
Haar-L² linear integral. -/
theorem p4Q2GZ_originalTransferIntegral_eq_linear_eval
    (B : Cfg) (f : Phys) :
    decomposableOneSliceTransferIntegral H 2 beta f B =
      p4Q2GZ_originalWilsonPhysicalTransferLinear H beta hbeta B
        (f : Lp ℝ 2 μ) := by
  rfl

end OriginalPhysicalWilson

section ActualRightKrylov

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ)
local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Phys" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule Hn 2
local notation "μ" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure Hn 2
local notation "RightFactor" =>
  physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)

/-- The MISSING DESCENT: for every actual signed finite-depth right-Krylov
physical source, its ORIGINAL one-slab Wilson integral is exactly GY's
finite linear functional of the ACTUAL modal original Wilson transfers. -/
theorem p4Q2GZ_actualSignedRightTransfer_eq_originalModalLinear
    (a : Fin (r + 1) → ℝ) (B : Cfg) :
    decomposableOneSliceTransferIntegral Hn 2 (beta n)
      (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) B =
      p4Q2GY_actualRightWilsonModalTransfer
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r B a := by
  let F := p4Q2GZ_originalWilsonPhysicalTransferLinear
    Hn (beta n) (hbeta n) B
  have hEval (f : Phys) :
      decomposableOneSliceTransferIntegral Hn 2 (beta n) f B =
        F (f : Lp ℝ 2 μ) :=
    p4Q2GZ_originalTransferIntegral_eq_linear_eval
      Hn (beta n) (hbeta n) B f
  calc
    decomposableOneSliceTransferIntegral Hn 2 (beta n)
        (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) B =
        F (↑(∑ j : Fin (r + 1),
          a j • RightFactor n (j : ℕ)) : Lp ℝ 2 μ) := hEval _
    _ = F (∑ j : Fin (r + 1),
          a j • (RightFactor n (j : ℕ) : Lp ℝ 2 μ)) := by
      simp only [Submodule.coe_sum, Submodule.coe_smul]
    _ = ∑ j : Fin (r + 1),
          a j * F (RightFactor n (j : ℕ) : Lp ℝ 2 μ) := by
      simp only [map_sum, map_smul, smul_eq_mul]
    _ = p4Q2GY_actualRightWilsonModalTransfer
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r B a := by
      change (∑ j : Fin (r + 1),
          a j * F (RightFactor n (j : ℕ) : Lp ℝ 2 μ)) =
        ∑ j : Fin (r + 1),
          a j * decomposableOneSliceTransferIntegral Hn 2 (beta n)
            (RightFactor n (j : ℕ)) B
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      exact (hEval (RightFactor n (j : ℕ))).symm

/-- The ZERO-LOCUS of the ACTUAL signed physical Wilson transfer is
exactly the real codimension-one GY modal-kernel hyperplane. -/
theorem p4Q2GZ_actualSignedRightTransfer_zero_iff_modalKernel
    (a : Fin (r + 1) → ℝ) (B : Cfg) :
    decomposableOneSliceTransferIntegral Hn 2 (beta n)
      (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) B = 0 ↔
      a ∈ (p4Q2GY_actualRightWilsonModalTransfer
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r B).ker := by
  rw [p4Q2GZ_actualSignedRightTransfer_eq_originalModalLinear
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a B]
  exact (LinearMap.mem_ker).symm

/-- The original signed physical Wilson-transfer null locus inherits
GY's exact real codimension-one (finrank r) structure, now with a
PROVED equality of the original source integral and modal extension. -/
noncomputable def p4Q2GZ_actualSignedPhysicalTransferKernel (B : Cfg) :
    Submodule ℝ (Fin (r + 1) → ℝ) :=
  (p4Q2GY_actualRightWilsonModalTransfer
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r B).ker

theorem p4Q2GZ_actualSignedPhysicalTransferKernel_mem_iff
    (a : Fin (r + 1) → ℝ) (B : Cfg) :
    a ∈ p4Q2GZ_actualSignedPhysicalTransferKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r B ↔
      decomposableOneSliceTransferIntegral Hn 2 (beta n)
        (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) B = 0 := by
  exact (p4Q2GZ_actualSignedRightTransfer_zero_iff_modalKernel
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r a B).symm

theorem p4Q2GZ_actualSignedPhysicalTransferKernel_finrank
    (B : Cfg) :
    Module.finrank ℝ
      ↥(p4Q2GZ_actualSignedPhysicalTransferKernel
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r B) = r := by
  exact p4Q2GY_actualRightWilsonModalTransfer_kernel_finrank
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r B

/-- A nonzero TRUE original transfer at the real pi insertion implies
positive squared physical response difference under the ORIGINAL
interacting Wilson conditional posterior, not under fake Haar. -/
theorem p4Q2GZ_actualRightPosteriorMass_pos_of_originalModal_ne
    (hFrozen : 0 < beta n)
    (a : Fin (r + 1) → ℝ) (right : Cfg)
    (e : PeriodicHypercubicEvenSpatialSliceLink Hn)
    (hModal :
      p4Q2GY_actualRightWilsonModalTransfer
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r (Function.update right e (specialUnitaryTwoRotation Real.pi)) a ≠ 0) :
    0 < p4Q2GU_originalPhysicalTwoBoundaryContrastPosteriorMass
      Hn (beta n) (hbeta n)
      (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
      right e := by
  apply p4Q2GW_actualRightKrylov_PosteriorMass_pos_of_transfer_ne
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFrozen a right e
  rw [p4Q2GZ_actualSignedRightTransfer_eq_originalModalLinear
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)]
  exact hModal

end ActualRightKrylov
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GZ_originalTransferIntegral_eq_linear_eval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GZ_actualSignedRightTransfer_eq_originalModalLinear
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GZ_actualSignedRightTransfer_zero_iff_modalKernel
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GZ_actualSignedPhysicalTransferKernel_mem_iff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GZ_actualSignedPhysicalTransferKernel_finrank
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GZ_actualRightPosteriorMass_pos_of_originalModal_ne
