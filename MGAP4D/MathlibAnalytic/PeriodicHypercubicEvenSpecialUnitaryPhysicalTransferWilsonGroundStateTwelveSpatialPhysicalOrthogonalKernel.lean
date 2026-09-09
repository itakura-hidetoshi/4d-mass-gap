import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointTwelveSpatialResidualKernel
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopEigenspaceContraction
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Filter
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

section FiniteVolume

variable (H N : ℕ)
variable (hN : 0 < N)
variable (beta : ℝ)
variable (hbeta : 0 ≤ beta)

local instance groundStatePhysicalOrthogonalVacuumProbability :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure_isProbabilityMeasure
    H N hN beta hbeta

local instance groundStatePhysicalOrthogonalJointProbability :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_isProbabilityMeasure
    H N hN beta hbeta

local notation "HaarL2" =>
  Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
local notation "G" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N
local notation "F" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
    H N hN beta hbeta
local notation "K" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
    H N hN beta hbeta
local notation "V" =>
  PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateVacuumL2
    H N hN beta hbeta
local notation "J" =>
  PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
    H N hN beta hbeta
local notation "U" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry
    H N hN beta hbeta
local notation "R" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift
    H N hN beta hbeta
local notation "Omega" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
    H N hN beta hbeta

set_option maxHeartbeats 1000000

/-- The ground-state transform sends the canonical strictly positive physical
top vector to the constant-one vector in the vacuum-weighted `L²` carrier.
This is the exact Hilbert-space form of the pointwise identity `Omega/Omega = 1`;
strict positivity is used only almost everywhere. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuum_nonnegativeTop_eq_const_one :
    U ((Omega : G) : HaarL2) =
      Lp.const 2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta) (1 : ℝ) := by
  let mu := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let nu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
      H N hN beta hbeta
  let omega : HaarL2 := (Omega : G)
  have hnu_mu : nu ≪ mu := by
    simpa [nu, mu] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure_absolutelyContinuous_Haar
        H N hN beta hbeta
  have hpos :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_ae_pos
      H N hN beta hbeta
  have hquot_mu :
      (fun A => omega A / omega A) =ᵐ[mu] (fun _ => (1 : ℝ)) :=
    hpos.mono fun A hA => div_self (ne_of_gt hA)
  have hquot_nu :
      (fun A => omega A / omega A) =ᵐ[nu] (fun _ => (1 : ℝ)) :=
    hnu_mu.ae_eq hquot_mu
  have hU :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2_coeFn
      H N hN beta hbeta omega
  have hUone :
      U omega =ᵐ[nu] (fun _ => (1 : ℝ)) := by
    exact hU.trans (by
      simpa [omega,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumFunction,
        mu, nu] using hquot_nu)
  have hone :=
    Lp.coeFn_const (μ := nu) (p := 2) (c := (1 : ℝ))
  apply Lp.ext
  exact hUone.trans hone.symm

/-- After the genuine right-boundary pullback, the transformed positive top
vector is exactly the intrinsic constant-one vector of the Wilson ground-state
joint `L²` carrier.  No top-eigenspace simplicity is used. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundary_nonnegativeTop_eq_constantL2_one :
    R (U ((Omega : G) : HaarL2)) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantL2
        H N hN beta hbeta 1 := by
  let nu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
      H N hN beta hbeta
  let pi :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
      H N hN beta hbeta
  let oneV : V := Lp.const 2 nu (1 : ℝ)
  have hUone :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuum_nonnegativeTop_eq_const_one
      H N hN beta hbeta
  have hsnd :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_snd_measurePreserving
      H N hN beta hbeta
  have hR :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryL2Isometry
          H N hN beta hbeta oneV =ᵐ[pi]
        fun z => oneV z.2 := by
    simpa [Function.comp_def] using
      (MeasureTheory.Lp.coeFn_compMeasurePreserving oneV hsnd)
  have honeV : (fun z => oneV z.2) =ᵐ[pi] (fun _ => (1 : ℝ)) := by
    have hbase := Lp.coeFn_const (μ := nu) (p := 2) (c := (1 : ℝ))
    simpa [Function.comp_def, oneV] using
      hbase.comp_tendsto hsnd.quasiMeasurePreserving.tendsto_ae
  have honeJ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantL2_coeFn
      H N hN beta hbeta 1
  rw [hUone]
  change
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryL2Isometry
        H N hN beta hbeta oneV =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantL2
        H N hN beta hbeta 1
  apply Lp.ext
  exact hR.trans (honeV.trans honeJ.symm)

/-- Qualitative definiteness on the genuine physical excitation sector.
For a vector orthogonal to the *full* normalized physical top eigenspace, the
twelve genuine spatial conditional-expectation residuals vanish exactly at the
zero vector after the ground-state transform and right-boundary lift.

This statement is strictly qualitative: it introduces no Poincare constant,
no scale-uniform coercivity, and no vacuum-uniqueness assumption. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy_rightBoundary_topOrthogonal_eq_zero_iff
    (x : K) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy
        H N hN beta hbeta
        (R (U (((x : G) : HaarL2)))) = 0 ↔
      x = 0 := by
  constructor
  · intro hzero
    rcases
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy_eq_zero_iff_eq_constantL2
        H N hN beta hbeta (R (U (((x : G) : HaarL2))))).1 hzero with
      ⟨c, hc⟩
    have hRU :
        R (U (((x : G) : HaarL2))) =
          R (c • U ((Omega : G) : HaarL2)) := by
      calc
        R (U (((x : G) : HaarL2))) =
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantL2
              H N hN beta hbeta c := hc
        _ = c •
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantL2
              H N hN beta hbeta 1 :=
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantL2_eq_smul_one
            H N hN beta hbeta c
        _ = c • R (U ((Omega : G) : HaarL2)) := by
          rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundary_nonnegativeTop_eq_constantL2_one
            H N hN beta hbeta]
        _ = R (c • U ((Omega : G) : HaarL2)) := by
          rw [map_smul]
    have hUeq :
        U (((x : G) : HaarL2)) = c • U ((Omega : G) : HaarL2) := by
      apply
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryL2Isometry
          H N hN beta hbeta).injective
      simpa [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift]
        using hRU
    have hHaar :
        (((x : G) : HaarL2)) = c • ((Omega : G) : HaarL2) := by
      apply
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry
          H N hN beta hbeta).injective
      simpa using hUeq
    have hxG : (x : G) = c • Omega := by
      apply Subtype.ext
      exact hHaar
    have hnorm :
        0 < ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
        H N hN beta hbeta
    have hOmegaF : Omega ∈ F := by
      rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_mem]
      rw [periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_apply,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_eigen]
      rw [smul_smul, inv_mul_cancel₀ hnorm.ne', one_smul]
    have hxF : (x : G) ∈ F := by
      rw [hxG]
      exact
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
          H N hN beta hbeta).smul_mem c hOmegaF
    have hxOrth : (x : G) ∈ Fᗮ := by
      simpa [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal]
        using x.property
    have hxBot : (x : G) ∈ (⊥ : Submodule ℝ G) := by
      have h :=
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
          H N hN beta hbeta).orthogonal_disjoint.le_bot ⟨hxF, hxOrth⟩
      simpa using h
    have hxGzero : (x : G) = 0 := by
      simpa using hxBot
    exact Subtype.ext hxGzero
  · rintro rfl
    simp [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy,
      groundStateJointColorNormalizedResidualEnergy]

end FiniteVolume

end

end MathlibAnalytic
end MGAP4D
