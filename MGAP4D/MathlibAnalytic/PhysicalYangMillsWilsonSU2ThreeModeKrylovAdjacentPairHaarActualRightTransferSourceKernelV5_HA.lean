import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarActualSourceTransferLinearityDescentV5_GZ
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarBetaZeroRightKrylovCollapse
import Mathlib.Tactic

/-!
# P4-Q2-HA: genuine Wilson boundary detection versus actual physical source kernel

GZ proved that the ORIGINAL physical Wilson one-slab transfer integral of
any signed right-Krylov source agrees with the real modal linear functional.
This file makes the distinction between its fixed-boundary hyperplane, its
whole-boundary joint kernel, and the kernel of the ACTUAL source synthesis.

* Source zero implies zero original Wilson transfer at every right boundary.
* The converse is stated ONLY with an explicit physical transfer-separation
  premise; no hidden strict-positive-definiteness/injectivity assumption.
* At actual fine coupling beta(n+1)=0, every fine right-Krylov vector equals
  its zero-depth physical constant unit. The source kernel and the original
  Wilson fixed-boundary modal kernel then BOTH equal the exact zero-sum
  coefficient hyperplane, unconditionally for ANY frozen beta(n)>=0.
* For frozen beta(n)>0, every coefficient vector with nonzero coefficient
  sum produces strictly positive TRUE interacting Wilson posterior
  two-LEFT-boundary response-square mass, on each actual physical link.

These are finite-volume source and transfer statements. This file does not
identify the two-Wilson-posterior expectation gap GI with the GZ response
contrast; does not assume all-depth Krylov linear independence, a uniform
physical frame, C1/C2/C3 reconstruction, or a continuum Yang--Mills gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 700000

local instance p4Q2HA_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2HA_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2HA_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2HA_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2HA_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

section AbstractFiniteSynthesis

variable {ι : Type*} [Fintype ι]
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A constant finite source family synthesizes EXACTLY the sum of its
real coefficients times the common source. No physical object is
unfolded in this elementary module theorem. -/
private theorem p4Q2HA_finiteSynthesis_of_constant
    (v : ι → E) (u : E) (hv : ∀ j, v j = u) (a : ι → ℝ) :
    (∑ j, a j • v j) = (∑ j, a j) • u := by
  calc
    (∑ j, a j • v j) = ∑ j, a j • u := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hv j]
    _ = (∑ j, a j) • u := (Finset.sum_smul).symm

/-- In a real module a constant-family synthesis has ONLY the
zero-sum coefficient obstruction provided its physical seed is nonzero. -/
private theorem p4Q2HA_finiteSynthesis_zero_iff
    (v : ι → E) (u : E) (hu : u ≠ 0)
    (hv : ∀ j, v j = u) (a : ι → ℝ) :
    (∑ j, a j • v j) = 0 ↔ (∑ j, a j) = 0 := by
  rw [p4Q2HA_finiteSynthesis_of_constant v u hv a]
  simp [hu]

end AbstractFiniteSynthesis

/-- Literal ORIGINAL Wilson one-slab transfer sends the ambient L² zero
input to zero; no synthetic reference measure is introduced. -/
private theorem p4Q2HA_originalWilsonTransfer_zero
    (H : ℕ) (beta : ℝ)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    decomposableOneSliceTransferIntegral H 2 beta
      (0 : Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) B = 0 := by
  rw [p4Q2GZ_originalTransferIntegral_eq_kernelIntegral]
  simp

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
local notation "Modal" =>
  p4Q2GY_actualRightWilsonModalTransfer
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r

/-- An ACTUAL physically vanishing signed right-Krylov source has zero
original Wilson modal transfer at EVERY actual right boundary. -/
theorem p4Q2HA_actualPhysicalSource_zero_implies_modal_zero
    (a : Fin (r + 1) → ℝ)
    (hSource :
      (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) = 0)
    (B : Cfg) :
    Modal B a = 0 := by
  have hAmbient :
      (↑(∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) :
        Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure Hn 2)) = 0 := by
    simpa only [Submodule.coe_zero] using congrArg Subtype.val hSource
  rw [← p4Q2GZ_actualSignedRightTransfer_eq_originalModalLinear
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a B]
  rw [hAmbient]
  exact p4Q2HA_originalWilsonTransfer_zero Hn (beta n) B

/-- Exact criterion for whole-boundary separation of the signed physical
source. Injectivity of the actual original Wilson transfer is an EXPLICIT
premise here, rather than an invented theorem about the Wilson kernel. -/
theorem p4Q2HA_jointModal_zero_iff_physicalSource_zero_of_separating
    (hSeparate :
      ∀ f : Phys,
        (∀ B : Cfg,
          decomposableOneSliceTransferIntegral Hn 2 (beta n) f B = 0) →
          f = 0)
    (a : Fin (r + 1) → ℝ) :
    (∀ B : Cfg, Modal B a = 0) ↔
      (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) = 0 := by
  constructor
  · intro hAll
    apply hSeparate
    intro B
    exact (p4Q2GZ_actualSignedRightTransfer_eq_originalModalLinear
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a B).trans (hAll B)
  · intro hSource B
    exact p4Q2HA_actualPhysicalSource_zero_implies_modal_zero
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a hSource B

/-- At ACTUAL fine beta(n+1)=0, the complete signed physical right-Krylov
source is precisely its scalar coefficient sum times the true physical
zero-depth unit vector. The distinct frozen beta(n) is unrestricted. -/
theorem p4Q2HA_fineZero_actualSource_eq_sum_smul
    (hFineZero : beta (n + 1) = 0)
    (a : Fin (r + 1) → ℝ) :
    (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) =
      (∑ j : Fin (r + 1), a j) • RightFactor n 0 := by
  apply p4Q2HA_finiteSynthesis_of_constant
  intro j
  exact fineRightFactor_eq_zeroDepth_of_fine_beta_zero
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n (j : ℕ) hFineZero

/-- The physical zero-depth right source is genuinely NONZERO at every
fine coupling; its norm is exactly one in the physical Hilbert space. -/
theorem p4Q2HA_actualZeroDepthSource_ne_zero :
    RightFactor n 0 ≠ 0 := by
  have hnorm : ‖RightFactor n 0‖ = (1 : ℝ) := by
    rw [fineRightFactor_zeroDepth_eq_constantUnit_anyFineBeta
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n]
    exact periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_norm Hn 2
  intro hz
  rw [hz, norm_zero] at hnorm
  norm_num at hnorm

/-- EXACT physical synthesis kernel at fine beta=0. For every finite
right-Krylov depth, source vanishing means coefficient SUM zero,
not that every signed coefficient is zero. -/
theorem p4Q2HA_fineZero_actualSource_zero_iff_sum_zero
    (hFineZero : beta (n + 1) = 0)
    (a : Fin (r + 1) → ℝ) :
    (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) = 0 ↔
      (∑ j : Fin (r + 1), a j) = 0 := by
  exact p4Q2HA_finiteSynthesis_zero_iff
    (fun j : Fin (r + 1) => RightFactor n (j : ℕ))
    (RightFactor n 0)
    (p4Q2HA_actualZeroDepthSource_ne_zero
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r)
    (fun j => fineRightFactor_eq_zeroDepth_of_fine_beta_zero
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n (j : ℕ) hFineZero)
    a

/-- Under actual fine beta=0, each TRUE Wilson modal coefficient
sample is the same positive frozen one-slab transfer of the zero
physical source mode. The exact value is the coefficient sum times
that genuine original Wilson sample. -/
theorem p4Q2HA_fineZero_originalModal_eq_sum_mul
    (hFineZero : beta (n + 1) = 0)
    (a : Fin (r + 1) → ℝ) (B : Cfg) :
    Modal B a =
      (∑ j : Fin (r + 1), a j) *
        decomposableOneSliceTransferIntegral Hn 2 (beta n)
          (RightFactor n 0) B := by
  change p4Q2GY_modalTransferLinear r
    (fun j : Fin (r + 1) =>
      decomposableOneSliceTransferIntegral Hn 2 (beta n)
        (RightFactor n (j : ℕ)) B) a = _
  rw [p4Q2GY_modalTransferLinear_apply]
  calc
    (∑ j : Fin (r + 1), a j *
      decomposableOneSliceTransferIntegral Hn 2 (beta n)
        (RightFactor n (j : ℕ)) B) =
      ∑ j : Fin (r + 1), a j *
        decomposableOneSliceTransferIntegral Hn 2 (beta n)
          (RightFactor n 0) B := by
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (fun t : ℝ => a j * t)
        (congrArg (fun f : Phys =>
          decomposableOneSliceTransferIntegral Hn 2 (beta n) f B)
          (fineRightFactor_eq_zeroDepth_of_fine_beta_zero
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n (j : ℕ) hFineZero))
    _ = (∑ j : Fin (r + 1), a j) *
        decomposableOneSliceTransferIntegral Hn 2 (beta n)
          (RightFactor n 0) B := (Finset.sum_mul).symm

/-- Fine-beta-zero original Wilson transfer vanishes at a fixed
physical right boundary IFF the signed coefficient sum vanishes.
The nonzero factor is the actual strictly positive Wilson transfer
of the physical constant unit, NOT an assumed source-frame constant. -/
theorem p4Q2HA_fineZero_originalModal_zero_iff_sum_zero
    (hFineZero : beta (n + 1) = 0)
    (a : Fin (r + 1) → ℝ) (B : Cfg) :
    Modal B a = 0 ↔ (∑ j : Fin (r + 1), a j) = 0 := by
  rw [p4Q2HA_fineZero_originalModal_eq_sum_mul
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFineZero a B]
  have hPos :
      0 < decomposableOneSliceTransferIntegral Hn 2 (beta n)
        (RightFactor n 0) B :=
    p4Q2GV_actualFineRightZeroMode_transferIntegral_pos
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n B
  simp [hPos.ne']

/-- At fine beta=0, the ORIGINAL physical Wilson transfer detector has
EXACTLY the true physical coefficient-source kernel at EVERY fixed B.
This unconditional endpoint theorem needs NO global transfer
injectivity premise and records the genuine rank-collapse obstruction. -/
theorem p4Q2HA_fineZero_modalKernel_iff_physicalSource_zero
    (hFineZero : beta (n + 1) = 0)
    (a : Fin (r + 1) → ℝ) (B : Cfg) :
    a ∈ (Modal B).ker ↔
      (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) = 0 := by
  rw [LinearMap.mem_ker]
  rw [p4Q2HA_fineZero_originalModal_zero_iff_sum_zero
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFineZero a B]
  exact (p4Q2HA_fineZero_actualSource_zero_iff_sum_zero
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFineZero a).symm

/-- For any nonzero signed coefficient SUM at fine beta=0 and any
positive frozen beta(n), the ORIGINAL interacting Wilson posterior
two-left-boundary response-square mass is STRICTLY positive for EVERY
actual physical right configuration and EVERY actual physical link. -/
theorem p4Q2HA_fineZero_originalPosteriorMass_pos_of_sum_ne
    (hFrozen : 0 < beta n)
    (hFineZero : beta (n + 1) = 0)
    (a : Fin (r + 1) → ℝ)
    (hSum : (∑ j : Fin (r + 1), a j) ≠ 0)
    (right : Cfg) (e : PeriodicHypercubicEvenSpatialSliceLink Hn) :
    0 < p4Q2GU_originalPhysicalTwoBoundaryContrastPosteriorMass
      Hn (beta n) (hbeta n)
      (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
      right e := by
  apply p4Q2GZ_actualRightPosteriorMass_pos_of_originalModal_ne
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFrozen a right e
  intro hModal
  apply hSum
  exact (p4Q2HA_fineZero_originalModal_zero_iff_sum_zero
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFineZero a
    (Function.update right e (specialUnitaryTwoRotation Real.pi))).mp hModal

end ActualRightKrylov
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HA_actualPhysicalSource_zero_implies_modal_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HA_jointModal_zero_iff_physicalSource_zero_of_separating
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HA_fineZero_actualSource_eq_sum_smul
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HA_actualZeroDepthSource_ne_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HA_fineZero_actualSource_zero_iff_sum_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HA_fineZero_originalModal_eq_sum_mul
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HA_fineZero_originalModal_zero_iff_sum_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HA_fineZero_modalKernel_iff_physicalSource_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HA_fineZero_originalPosteriorMass_pos_of_sum_ne
