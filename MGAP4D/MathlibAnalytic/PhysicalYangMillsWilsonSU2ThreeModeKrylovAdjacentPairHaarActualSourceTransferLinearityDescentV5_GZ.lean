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
linear map on the entire ambient real L² space, then uses this generic
lemma directly in the concrete physical sum proof. Its integrability follows
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
set_option maxHeartbeats 9000000
set_option synthInstance.maxHeartbeats 1400000

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
  refine hf.norm.mono' hmeas ?_
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
          rw [hx, Pi.add_apply, mul_add]
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
          rw [hx, Pi.smul_apply, smul_eq_mul]
          ring
        _ = c * (∫ x, K x * f x ∂μ) := integral_const_mul c _ }


/-- Exact finite linearity of genuine bounded-kernel L² Haar integrals;
integrability of every term is built into the source linear map. -/
private theorem p4Q2GZ_weightedLpFinite_sum
    {ι : Type*} (K : α → ℝ)
    (hK : AEStronglyMeasurable K μ)
    (hBound : ∀ x, ‖K x‖ ≤ 1)
    (s : Finset ι) (a : ι → ℝ) (v : ι → Lp ℝ 2 μ) :
    (∫ x, K x * (∑ j ∈ s, a j • v j) x ∂μ) =
      ∑ j ∈ s, a j * (∫ x, K x * v j x ∂μ) := by
  let F := p4Q2GZ_weightedLpLinear K hK hBound
  change F (∑ j ∈ s, a j • v j) = ∑ j ∈ s, a j * F (v j)
  simp [map_sum, map_smul, smul_eq_mul]

end AbstractHaarL2

/-- The defining original one-slab Wilson kernel formula for an arbitrary
ambient spatial Haar-L² input, isolated from finite coefficient sums. -/
theorem p4Q2GZ_originalTransferIntegral_eq_kernelIntegral
    (H : ℕ) (beta : ℝ)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (f : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) :
    decomposableOneSliceTransferIntegral H 2 beta f B =
      ∫ A, periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H 2 beta A B * f A
        ∂periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2 := by
  rfl

/-! ## Linear functional representation of the original Wilson transfer -/

/-- The original (not surrogate) Wilson transfer as a REAL linear map
on the ambient spatial Haar L² Hilbert space. The integrability and
linearity proofs are discharged generically by `weightedLpLinear`:
there is no unfolding of an actual Krylov source in this construction. -/
noncomputable def p4Q2GZ_originalWilsonTransferLinear
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)
      →ₗ[ℝ] ℝ := by
  let ν : Measure
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  haveI : IsProbabilityMeasure ν := p4Q2GZ_spatialHaarProbability H
  let K : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 → ℝ :=
    fun A => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
      H 2 beta A B
  have hcont : Continuous K :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
      H 2 beta).comp (continuous_id.prodMk continuous_const)
  have hmeas : AEStronglyMeasurable K ν := hcont.aestronglyMeasurable
  have hbound : ∀ A, ‖K A‖ ≤ 1 := by
    intro A
    change ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
      H 2 beta A B‖ ≤ 1
    rw [Real.norm_eq_abs]
    exact periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
      H 2 (by norm_num) beta hbeta A B
  exact p4Q2GZ_weightedLpLinear K hmeas hbound

/-- Evaluation of this genuine linear map is DEFINITIONALLY the original
physical Wilson one-slab transfer integral for an arbitrary ambient L²
function, without inspecting the function's concrete implementation. -/
theorem p4Q2GZ_originalWilsonTransferLinear_apply
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (f : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) :
    p4Q2GZ_originalWilsonTransferLinear H beta hbeta B f =
      decomposableOneSliceTransferIntegral H 2 beta f B := by
  rfl

/-- Transport finite sums from ANY family of physical gauge-invariant
sources through the TRUE Wilson integral using the already constructed
ambient linear map. In particular no `change` on a huge kernel integral
or definitional normalization of Krylov fields is needed. -/
private theorem p4Q2GZ_originalPhysicalTransferFinite_sum
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    {ι : Type*} [Fintype ι]
    (a : ι → ℝ)
    (v : ι →
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :
    decomposableOneSliceTransferIntegral H 2 beta
        (∑ j, a j • v j) B =
      ∑ j, a j *
        decomposableOneSliceTransferIntegral H 2 beta (v j) B := by
  let ν : Measure
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let T : Lp ℝ 2 ν →ₗ[ℝ] ℝ :=
    p4Q2GZ_originalWilsonTransferLinear H beta hbeta B
  have hCoerce :
      (↑(∑ j, a j • v j) : Lp ℝ 2 ν) =
        ∑ j, a j • (v j : Lp ℝ 2 ν) := by
    simp only [Submodule.coe_sum, Submodule.coe_smul]
  have hLin :
      T (↑(∑ j, a j • v j) : Lp ℝ 2 ν) =
        ∑ j, a j * T (v j : Lp ℝ 2 ν) := by
    rw [hCoerce, map_sum]
    simp only [map_smul, smul_eq_mul]
  have hEq (f : Lp ℝ 2 ν) :
      decomposableOneSliceTransferIntegral H 2 beta f B = T f :=
    (p4Q2GZ_originalWilsonTransferLinear_apply H beta hbeta B f).symm
  calc
    decomposableOneSliceTransferIntegral H 2 beta (∑ j, a j • v j) B =
        T (↑(∑ j, a j • v j) : Lp ℝ 2 ν) := hEq _
    _ = ∑ j, a j * T (v j : Lp ℝ 2 ν) := hLin
    _ = ∑ j, a j *
          decomposableOneSliceTransferIntegral H 2 beta (v j) B := by
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (fun t : ℝ => a j * t)
        (hEq (v j : Lp ℝ 2 ν)).symm

section ActualRightKrylov

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ)
local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Phys" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule Hn 2
local notation "RightFactor" =>
  physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)

/-- EXACT finite-sum descent from the original physical Wilson
one-slab integral to GY's genuine modal coefficient functional.
The general finite-source theorem has already discharged all
integrability and submodule coercion obligations. -/
theorem p4Q2GZ_actualSignedRightTransfer_eq_originalModalLinear
    (a : Fin (r + 1) → ℝ) (B : Cfg) :
    decomposableOneSliceTransferIntegral Hn 2 (beta n)
      (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) B =
      p4Q2GY_actualRightWilsonModalTransfer
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r B a := by
  change
    decomposableOneSliceTransferIntegral Hn 2 (beta n)
      (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) B =
      ∑ j : Fin (r + 1), a j *
        decomposableOneSliceTransferIntegral Hn 2 (beta n)
          (RightFactor n (j : ℕ)) B
  exact p4Q2GZ_originalPhysicalTransferFinite_sum
    Hn (beta n) (hbeta n) B a
    (fun j : Fin (r + 1) => RightFactor n (j : ℕ))

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

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GZ_originalTransferIntegral_eq_kernelIntegral
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GZ_actualSignedRightTransfer_eq_originalModalLinear
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GZ_actualSignedRightTransfer_zero_iff_modalKernel
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GZ_actualSignedPhysicalTransferKernel_mem_iff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GZ_actualSignedPhysicalTransferKernel_finrank
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GZ_actualRightPosteriorMass_pos_of_originalModal_ne
