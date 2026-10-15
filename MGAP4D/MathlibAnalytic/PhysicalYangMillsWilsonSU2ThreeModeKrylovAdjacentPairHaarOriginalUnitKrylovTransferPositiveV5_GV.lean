import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTwoBoundarySignedResponseHaarPositiveV5_GT
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarAnyFineZeroModePositive
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalConstantPhysicalKrylovTransferPositiveV5_GV
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTwoBoundaryPhysicalContrastWilsonPosteriorMassV5_GU
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

This is a genuine SINGLE right-Krylov ZERO-MODE detector on the reference
Haar carrier AND the original interacting Wilson conditional posterior.
It does not establish GI two-posterior signed expectation-gap injectivity,
a coefficient-source frame, or an H-uniform lower
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

/-- The original Wilson kernel has positive Haar integral for every physical
right boundary.  Reuse the independently checked physical constant-unit
transfer theorem, preserving the exact kernel-integral identity.  In this
large concrete lattice type, re-expanding the compactness minimum here
causes repeated weak-head reduction timeouts. -/
theorem p4Q2GVUnit_originalKernelIntegral_pos
    (H : ℕ) (beta : ℝ)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    0 < ∫ A,
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H 2 beta A B
      ∂periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2 := by
  calc
    0 < decomposableOneSliceTransferIntegral H 2 beta
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2) B :=
      p4Q2GV_originalConstantPhysicalTransferIntegral_pos H beta B
    _ = ∫ A,
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H 2 beta A B
          ∂periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2 :=
      p4Q2GVUnit_originalPhysicalUnit_transfer_eq_kernelIntegral H beta B

/-- The actual Wilson transfer of the gauge-invariant constant unit is
strictly positive at EVERY real right boundary configuration and every
finite volume, independent of the frozen beta sign. -/
theorem p4Q2GV_originalPhysicalUnit_transferIntegral_pos
    (H : ℕ) (beta : ℝ)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    0 < decomposableOneSliceTransferIntegral H 2 beta
      (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2) B := by
  exact p4Q2GV_originalConstantPhysicalTransferIntegral_pos H beta B

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

/-- For the genuine physical constant unit, the original interacting
identity-left Wilson conditional posterior—not independent Haar—assigns
strictly positive squared mass to the original two-left-boundary
signed response difference at every positive frozen beta. -/
theorem p4Q2GV_originalPhysicalUnit_twoBoundaryWilsonPosteriorMass_pos
    (H : ℕ) (beta : ℝ) (hpos : 0 < beta)
    (right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    0 < p4Q2GU_originalPhysicalTwoBoundaryContrastPosteriorMass
      H beta (le_of_lt hpos)
      (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)
      right e := by
  exact p4Q2GU_originalPhysicalContrastPosteriorMass_pos_of_transfer
    H beta (le_of_lt hpos) hpos
    (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)
    right e
    (p4Q2GV_originalConstantPhysicalTransferIntegral_pos H beta
      (Function.update right e (specialUnitaryTwoRotation Real.pi)))

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

/-- The exact interacting original Wilson posterior mass dominates
the compact SU(2) Haar reference squared difference for the SAME actual
fine right Krylov zero-depth physical source, at the frozen beta(n). -/
theorem p4Q2GV_actualFineRightZeroMode_twoBoundaryWilsonPosteriorMass_ge_Haar
    (right : Cfg) (e : Link) :
    Real.exp (-16 * beta n) *
        p4Q2GT_originalTwoBoundaryPhysicalSignedResponseHaarMass
          Hn (beta n) (hbeta n) (RightFactor n 0) right e ≤
      p4Q2GU_originalPhysicalTwoBoundaryContrastPosteriorMass
        Hn (beta n) (hbeta n) (RightFactor n 0) right e := by
  exact p4Q2GU_originalPhysicalContrastPosteriorMass_ge_Haar
    Hn (beta n) (hbeta n) (RightFactor n 0) right e

/-- At strictly positive frozen beta(n), the real fine right Krylov
zero mode has unconditionally positive original interacting Wilson
posterior squared two-boundary response mass.  No assumed signed source
frame, fake Haar conditional law or positive transfer witness remains. -/
theorem p4Q2GV_actualFineRightZeroMode_twoBoundaryWilsonPosteriorMass_pos
    (hFrozen : 0 < beta n) (right : Cfg) (e : Link) :
    0 < p4Q2GU_originalPhysicalTwoBoundaryContrastPosteriorMass
      Hn (beta n) (hbeta n) (RightFactor n 0) right e := by
  have hHaar :
      0 < p4Q2GT_originalTwoBoundaryPhysicalSignedResponseHaarMass
        Hn (beta n) (hbeta n) (RightFactor n 0) right e :=
    p4Q2GV_actualFineRightZeroMode_twoBoundaryHaarMass_pos
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen right e
  have hBound :
      Real.exp (-16 * beta n) *
          p4Q2GT_originalTwoBoundaryPhysicalSignedResponseHaarMass
            Hn (beta n) (hbeta n) (RightFactor n 0) right e ≤
        p4Q2GU_originalPhysicalTwoBoundaryContrastPosteriorMass
          Hn (beta n) (hbeta n) (RightFactor n 0) right e :=
    p4Q2GV_actualFineRightZeroMode_twoBoundaryWilsonPosteriorMass_ge_Haar
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n right e
  exact lt_of_lt_of_le (mul_pos (Real.exp_pos _) hHaar) hBound

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
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GV_originalPhysicalUnit_twoBoundaryWilsonPosteriorMass_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GV_actualFineRightZeroMode_twoBoundaryWilsonPosteriorMass_ge_Haar
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GV_actualFineRightZeroMode_twoBoundaryWilsonPosteriorMass_pos
