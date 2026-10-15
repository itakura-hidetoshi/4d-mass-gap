import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTwoBoundarySignedResponseHaarPositiveV5_GT
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarAnyFineZeroModePositive
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferStrictlyPositiveTopEigenvector
import Mathlib.Tactic

/-!
# P4-Q2-GV: unconditional original Wilson transfer positivity of the
actual physical right-Krylov zero mode, with no source-frame assumption

The *actual* right Krylov orbit begins at the exact gauge-invariant
physical constant unit, for every fine beta(n+1), by P4-Q2-M.
The genuine finite-volume original SU(2) Wilson one-slab kernel is
strictly positive, jointly continuous on compact physical pair
configurations, and admits a finite-volume strictly positive constant
lower bound c(H,beta) independently of its two boundary arguments.

The TRUE original one-slab transfer integral of the actual physical
constant unit is the genuine Haar integral of that original kernel
because the unit vector has the constant-one L² representative
almost everywhere. Thus t_unit(B) >= c(H,beta) > 0 for ALL B.

There is no postulated physical source positivity: it is derived from
the exact original kernel and the actual physical constant Hilbert
source. Consequently GS/GT's true Wilson two-LEFT-boundary physical
signed response is nonzero at the literal SU2 pi insertion and has
strictly positive Haar reference squared mass, without any assumed
source transfer witness, for every positive frozen beta, physical link,
finite spatial volume and arbitrary fine beta(n+1).

This is a genuine SINGLE right-Krylov ZERO-MODE detector on a reference
Haar carrier, not yet the GI two-posterior signed expectation-gap
injectivity, or a coefficient-source frame, nor an H-uniform lower
c(H,beta), C1/C2/C3 or a continuum Yang--Mills mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 9000000
set_option synthInstance.maxHeartbeats 2000000

local instance p4Q2GVUnit_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2GVUnit_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2GVUnit_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2GVUnit_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2GVUnit_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance p4Q2GVUnit_haarProbability (H : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint

/-- Perform the probability integral comparison in a GENERIC measurable
space.  Elaborating this after substituting the gigantic concrete
SU(2) lattice configuration causes nonterminating weak-head reduction
at the kernel check. -/
private theorem p4Q2GV_integral_pos_of_uniform_floor
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ]
    {f : α → ℝ} (hf : Integrable f μ)
    {m : ℝ} (hm : 0 < m) (hFloor : ∀ a, m ≤ f a) :
    0 < ∫ a, f a ∂μ := by
  have hConst : (∫ _ : α, m ∂μ) = m := by
    simp
  have hBound : (∫ _ : α, m ∂μ) ≤ ∫ a, f a ∂μ := by
    apply integral_mono (integrable_const m) hf
    intro a
    exact hFloor a
  rw [hConst] at hBound
  exact lt_of_lt_of_le hm hBound


/-- The original continuous Wilson one-slab kernel has strictly positive
spatial-Haar integral.  Use the EXISTING concrete compact-kernel lower-bound
theorem and a direct integral monotonicity step; do not unfold the enormous
finite-volume gauge configuration to prove full-support positivity again. -/
theorem p4Q2GVUnit_originalKernelIntegral_pos
    (H : ℕ) (beta : ℝ)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    0 < ∫ A,
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H 2 beta A B
      ∂periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2 := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let K : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 → ℝ :=
    fun A => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta A B
  have hContinuous : Continuous K :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
      H 2 beta).comp (continuous_id.prodMk continuous_const)
  have hIntegrable : Integrable K μ :=
    hContinuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  obtain ⟨m, hmPos, hmLower⟩ :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_exists_uniform_pos_lower_bound
      H 2 beta
  haveI : IsProbabilityMeasure μ := by
    change IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)
    exact p4Q2GVUnit_haarProbability H
  change 0 < ∫ A, K A ∂μ
  exact p4Q2GV_integral_pos_of_uniform_floor
    (μ := μ) (f := K) hIntegrable hmPos (fun A => hmLower A B)

/-- The actual physical gauge-invariant constant unit is Haar-a.e.
one. Consequently its ORIGINAL smoothed Wilson transfer integral is
EXACTLY the integral of the true one-slab Wilson kernel. -/
theorem p4Q2GVUnit_originalPhysicalUnit_transfer_eq_kernelIntegral
    (H : ℕ) (beta : ℝ)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    decomposableOneSliceTransferIntegral H 2 beta
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2) B =
      ∫ A,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H 2 beta A B
        ∂periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2 := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let K := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta
  let oneP := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  have hUnitAE :
      (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 =>
        (oneP : Lp ℝ 2 μ) A) =ᵐ[μ] (fun _ => (1 : ℝ)) := by
    change (fun A => (Lp.const 2 μ (1 : ℝ)) A) =ᵐ[μ] (fun _ => (1 : ℝ))
    exact Lp.coeFn_const (μ := μ) (p := 2) (c := (1 : ℝ))
  change (∫ A, K A B * (oneP : Lp ℝ 2 μ) A ∂μ) =
    ∫ A, K A B ∂μ
  apply integral_congr_ae
  filter_upwards [hUnitAE] with A hA
  simp only [hA, mul_one]

/-- The actual Wilson transfer of the gauge-invariant constant unit is
strictly positive at EVERY real right boundary configuration and every
finite volume, independent of the frozen beta sign. -/
theorem p4Q2GV_originalPhysicalUnit_transferIntegral_pos
    (H : ℕ) (beta : ℝ)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    0 < decomposableOneSliceTransferIntegral H 2 beta
      (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2) B := by
  rw [p4Q2GVUnit_originalPhysicalUnit_transfer_eq_kernelIntegral]
  exact p4Q2GVUnit_originalKernelIntegral_pos H beta B

/-- No ad hoc positive source input is required for the ORIGINAL
Wilson constant-unit response: it is strict negative at the genuine
SU2 pi right insertion under the two true physical left boundaries. -/
theorem p4Q2GV_originalPhysicalUnit_twoBoundaryResponse_strict_neg
    (H : ℕ) (beta : ℝ) (hpos : 0 < beta)
    (right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    p4Q2GT_originalTwoBoundaryPhysicalSignedResponseDifference
      H beta (le_of_lt hpos)
      (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)
      right e (specialUnitaryTwoRotation Real.pi) < 0 := by
  exact p4Q2GS_originalPhysicalSource_twoBoundaryResponse_strict_neg
    H beta (le_of_lt hpos) hpos
    (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)
    right e
    (p4Q2GV_originalPhysicalUnit_transferIntegral_pos
      H beta (Function.update right e (specialUnitaryTwoRotation Real.pi)))

/-- The original Wilson physical unit source has strictly positive Haar
L² MASS of its ACTUAL signed two-boundary response difference for EVERY
genuine right physical link and every background at frozen beta>0. -/
theorem p4Q2GV_originalPhysicalUnit_twoBoundaryHaarMass_pos
    (H : ℕ) (beta : ℝ) (hpos : 0 < beta)
    (right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    0 < p4Q2GT_originalTwoBoundaryPhysicalSignedResponseHaarMass
      H beta (le_of_lt hpos)
      (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)
      right e := by
  exact p4Q2GT_originalPhysicalSignedTwoBoundaryHaarMass_pos_of_transfer
    H beta (le_of_lt hpos) hpos
    (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2) right e
    (p4Q2GV_originalPhysicalUnit_transferIntegral_pos
      H beta (Function.update right e (specialUnitaryTwoRotation Real.pi)))

section ActualAdjacent
variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n : ℕ)
local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "RightFactor" => physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)

/-- EXACT genuine fine right Krylov ZERO-DEPTH factor has positive
ORIGINAL frozen one-slab Wilson source transfer, without any
hypothesis on the fine beta(n+1) beyond the canonical nonnegativity. -/
theorem p4Q2GV_actualFineRightZeroMode_transferIntegral_pos
    (B : Cfg) :
    0 < decomposableOneSliceTransferIntegral Hn 2 (beta n)
      (RightFactor n 0) B := by
  rw [fineRightFactor_zeroDepth_eq_constantUnit_anyFineBeta n]
  exact p4Q2GV_originalPhysicalUnit_transferIntegral_pos Hn (beta n) B

/-- For each positive frozen coupling, every finite volume and physical
link, the ACTUAL fine right Krylov ZERO MODE has strict original
two-LEFT-boundary signed response separation in Haar L² without
assuming any positive physical source transfer condition. -/
theorem p4Q2GV_actualFineRightZeroMode_twoBoundaryHaarMass_pos
    (hFrozen : 0 < beta n) (right : Cfg) (e : Link) :
    0 < p4Q2GT_originalTwoBoundaryPhysicalSignedResponseHaarMass
      Hn (beta n) (hbeta n)
      (RightFactor n 0) right e := by
  have hUnit :
      RightFactor n 0 =
        periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector Hn 2 :=
    fineRightFactor_zeroDepth_eq_constantUnit_anyFineBeta n
  rw [hUnit]
  exact p4Q2GV_originalPhysicalUnit_twoBoundaryHaarMass_pos
    Hn (beta n) hFrozen right e

end ActualAdjacent
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GVUnit_originalKernelIntegral_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GVUnit_originalPhysicalUnit_transfer_eq_kernelIntegral
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GV_originalPhysicalUnit_transferIntegral_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GV_originalPhysicalUnit_twoBoundaryResponse_strict_neg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GV_originalPhysicalUnit_twoBoundaryHaarMass_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GV_actualFineRightZeroMode_transferIntegral_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GV_actualFineRightZeroMode_twoBoundaryHaarMass_pos
