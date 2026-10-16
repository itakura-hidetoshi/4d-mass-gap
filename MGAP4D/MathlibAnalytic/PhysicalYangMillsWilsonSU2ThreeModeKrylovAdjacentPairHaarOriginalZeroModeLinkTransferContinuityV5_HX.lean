import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarRelativeReceiverGapHellingerBridgeV5_HW
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalRelativePosteriorReceiverV5_GR
import Mathlib.Tactic

/-!
# P4-Q2-HX: original Wilson zero-mode right-link transfer continuity

GR's exact ORIGINAL Wilson relative half-density formula solves for the
genuine physical-source one-slab transfer on each right link in terms
of the actual continuous signed source FF receiver and the strictly
positive continuous original interacting Wilson normalized density.

Thus right-link continuity of the ORIGINAL transfer, for the concrete
zero-depth Krylov source (and indeed for any physical source accepted
by the original FF BCF construction), is DERIVED rather than assumed.
No independent Haar conditional, positive frame, or arbitrary source
injectivity is introduced.

This discharges the continuity input required by the already-verified
HV/HW two-density noncancellation for the physical zero-mode source.
The GI gap evaluation and nonvanishing are a separate subsequent gate.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Matrix

noncomputable section
set_option maxHeartbeats 3400000
set_option synthInstance.maxHeartbeats 950000

namespace GroundStatePosteriorJoint

/-- An exact positive-density relative receiver formula determines
the transfer function from the receiver by a pointwise identity.
In particular, continuity of the receiver and positive density FORCES
continuity of T, without dominated-convergence assumptions. -/
theorem p4Q2HX_transfer_continuous_of_positive_relative_receiver
    {X : Type*} [TopologicalSpace X]
    (T R P : X → ℝ) (L : ℝ) (h : X)
    (hR : Continuous R) (hP : Continuous P)
    (hPpos : ∀ g, 0 < P g) (hL : 0 < L)
    (hRelative : ∀ g,
      R g = L * (T h - Real.sqrt (P h) / Real.sqrt (P g) * T g)) :
    Continuous T := by
  have hEq (g : X) :
      T g =
        Real.sqrt (P g) / Real.sqrt (P h) *
          (T h - R g / L) := by
    have hr := hRelative g
    have hh : Real.sqrt (P h) ≠ 0 :=
      (Real.sqrt_pos.mpr (hPpos h)).ne'
    have hg : Real.sqrt (P g) ≠ 0 :=
      (Real.sqrt_pos.mpr (hPpos g)).ne'
    have hLn : L ≠ 0 := hL.ne'
    field_simp [hh, hg, hLn] at hr ⊢
    nlinarith [hr]
  have hFun :
      T = (fun g : X =>
        Real.sqrt (P g) / Real.sqrt (P h) * (T h - R g / L)) :=
    funext hEq
  rw [hFun]
  exact ((Real.continuous_sqrt.comp hP).div_const _).mul
    (continuous_const.sub (hR.div_const _))

local instance p4Q2HX_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2HX_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2HX_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2HX_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2HX_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

section ActualRight

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "RightFactor" =>
  physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)

/-- Original finite Wilson one-slab transfer of the ACTUAL zero-depth
fine-right Krylov source is continuous as the right SU(2) link varies.
The physical zero-mode is the constant unit for ALL fine beta(n+1)>=0.
The proof uses the ORIGINAL GR exact half-density receiver rather
than inserting a new transfer-regularity assumption. -/
theorem p4Q2HX_actualFineRightZeroDepth_originalWilsonTransfer_link_continuous
    (right : Cfg) (e : Link) :
    Continuous (fun g : Gauge =>
      decomposableOneSliceTransferIntegral Hn 2 (beta n)
        (RightFactor n 0) (Function.update right e g)) := by
  let μ : Measure Gauge := normalizedCompactHaar Gauge
  let left : Cfg := originalWilsonExplicitIdentityBoundary Hn
  let L : ℝ :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      Hn 2 (by norm_num) (beta n) (hbeta n)‖⁻¹
  let T : Gauge → ℝ := fun g =>
    decomposableOneSliceTransferIntegral Hn 2 (beta n)
      (RightFactor n 0) (Function.update right e g)
  let P : Gauge → ℝ := fun g =>
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
      Hn 2 (by norm_num) (beta n) (hbeta n) left right e g
  let R : Gauge → ℝ := fun g =>
    p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
      Hn 2 (by norm_num) (beta n) (hbeta n)
      (RightFactor n 0) e ((left, right), g)
  have hR : Continuous R := by
    dsimp [R]
    exact (p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
      Hn 2 (by norm_num) (beta n) (hbeta n)
      (RightFactor n 0) e).continuous.comp
        (continuous_const.prodMk continuous_id)
  have hP : Continuous P := by
    change Continuous
      (continuousNormalizedExp μ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
          Hn 2 (by norm_num) (beta n) (hbeta n) left right e))
    exact continuous_continuousNormalizedExp μ _
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_continuous
        Hn 2 (by norm_num) (beta n) (hbeta n) left right e)
  have hPpos (g : Gauge) : 0 < P g :=
    p4Q2GQ_originalPosteriorDensity_pos
      Hn (beta n) (hbeta n) left right e g
  have hL : 0 < L := by
    dsimp [L]
    exact inv_pos.mpr
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
        Hn 2 (by norm_num) (beta n) (hbeta n))
  have hUpdate : Function.update right e (right e) = right :=
    Function.update_eq_self e right
  have hRelative (g : Gauge) :
      R g = L * (T (right e) -
        Real.sqrt (P (right e)) / Real.sqrt (P g) * T g) := by
    have hGR :=
      p4Q2GR_originalSignedResponse_at_inserted_right
        Hn (beta n) (hbeta n) (RightFactor n 0)
        left right e g (right e)
    simpa only [hUpdate, R, L, P, T] using hGR
  exact p4Q2HX_transfer_continuous_of_positive_relative_receiver
    T R P L (right e) hR hP hPpos hL hRelative

end ActualRight
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HX_transfer_continuous_of_positive_relative_receiver
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HX_actualFineRightZeroDepth_originalWilsonTransfer_link_continuous
