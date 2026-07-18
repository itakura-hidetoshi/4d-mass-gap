import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanRayleighL2
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectorySpecialUnitaryTwoStapleOscillationSeparationBCF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators

noncomputable section

set_option maxRecDepth 8192

local instance periodicBetaZeroAttainmentSpecialUnitaryTwoNontrivial :
    Nontrivial (SpecialUnitaryMatrixGroup 2) :=
  ⟨⟨specialUnitaryTwoNegativeIdentity, 1,
    specialUnitaryTwoNegativeIdentity_ne_one⟩⟩

/-- The one-variable `SU(2)` Wilson energy read at the distinguished physical
link of the actual side-three endpoint system. -/
noncomputable def
    periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyBCF :
    BoundedContinuousFunction
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration ℝ := by
  let f :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration → ℝ :=
    fun A => specialUnitaryTwoWilsonEnergyBCF
      (A periodicHypercubicThreeOriginAxisZeroTarget)
  have hf : Continuous f := by
    exact specialUnitaryTwoWilsonEnergyBCF.continuous.comp
      (continuous_apply periodicHypercubicThreeOriginAxisZeroTarget)
  exact BoundedContinuousFunction.mkOfCompact ⟨f, hf⟩

@[simp]
theorem periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyBCF_apply
    (A : periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration) :
    periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyBCF A =
      specialUnitaryWilsonPlaquetteEnergy 2
        (A periodicHypercubicThreeOriginAxisZeroTarget) := by
  rfl

/-- Reading the distinguished coordinate is constant on every different
physical-link fiber. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyBCF_offLinkFiberConstant_of_ne
    (source :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hSource : source ≠ periodicHypercubicThreeOriginAxisZeroTarget) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.OffLinkFiberConstant
      source periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyBCF := by
  intro A B hAgree
  simp only [periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyBCF_apply]
  congr 1
  exact hAgree periodicHypercubicThreeOriginAxisZeroTarget (Ne.symm hSource)

/-- The distinguished-coordinate Wilson energy is not constant on its own
coordinate fibers: the identity and central negative identity give values zero
and two. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyBCF_not_offLinkFiberConstant :
    ¬ periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.OffLinkFiberConstant
      periodicHypercubicThreeOriginAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyBCF := by
  intro hFiber
  let A0 :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration :=
    fun _ => 1
  let A1 :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.replaceLink
      A0 periodicHypercubicThreeOriginAxisZeroTarget
      specialUnitaryTwoNegativeIdentity
  have hAgree :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.AgreeOffLink
        A0 A1 periodicHypercubicThreeOriginAxisZeroTarget := by
    intro edge hEdge
    simp [A1, hEdge]
  have hEq := hFiber A0 A1 hAgree
  norm_num [A0, A1] at hEq
  rw [specialUnitaryWilsonPlaquetteEnergy_two_one] at hEq
  norm_num at hEq

/-- Every other actual one-link heat-bath projection fixes the distinguished
coordinate observable already on the bounded-continuous core. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyBCF_projection_eq_self_of_ne
    (source :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hSource : source ≠ periodicHypercubicThreeOriginAxisZeroTarget) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionBCFOfBetaZero
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
        source periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyBCF =
      periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyBCF := by
  ext A
  exact congrFun
    (continuous_compact_oriented_singleLinkHeatBathProjection_fixes
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem source
      periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyBCF
      (periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyBCF_offLinkFiberConstant_of_ne
        source hSource)) A

/-- Consequently every other one-link projection fixes the actual Gibbs `L²`
representative of the distinguished-coordinate observable. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyL2_projection_eq_self_of_ne
    (source :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hSource : source ≠ periodicHypercubicThreeOriginAxisZeroTarget) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionL2
        source
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsL2RepresentativeBCF
          periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyBCF) =
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsL2RepresentativeBCF
        periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyBCF := by
  rw [continuous_compact_oriented_singleLinkHeatBathProjectionL2_gibbsL2RepresentativeBCF_of_beta_eq_zero
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
    source periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyBCF]
  rw [periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyBCF_projection_eq_self_of_ne
    source hSource]

/-- The distinguished-link fluctuation of the target-coordinate Wilson energy. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkFluctuationL2 :
    Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure :=
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
    periodicHypercubicThreeOriginAxisZeroTarget
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsL2RepresentativeBCF
      periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyBCF)

/-- The distinguished-link fluctuation is nonzero.  Otherwise injectivity of
bounded-continuous representatives in the full-support Gibbs `L²` space would
force the nonconstant coordinate observable to be fixed by its own Haar
projection. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkFluctuationL2_ne_zero :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkFluctuationL2 ≠ 0 := by
  intro hZero
  let C := periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
  let target := periodicHypercubicThreeOriginAxisZeroTarget
  let O := periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyBCF
  have hSub :
      C.gibbsL2RepresentativeBCF O =
        C.singleLinkHeatBathProjectionL2 target
          (C.gibbsL2RepresentativeBCF O) := by
    apply sub_eq_zero.mp
    simpa [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkFluctuationL2,
      C, target, O,
      continuous_compact_oriented_singleLinkHeatBathFluctuationL2_apply] using hZero
  have hProjection :=
    continuous_compact_oriented_singleLinkHeatBathProjectionL2_gibbsL2RepresentativeBCF_of_beta_eq_zero
      C periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero target O
  have hRepresentatives :
      C.gibbsL2RepresentativeBCF O =
        C.gibbsL2RepresentativeBCF
          (C.singleLinkHeatBathProjectionBCFOfBetaZero
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero target O) :=
    hSub.trans hProjection
  change
    BoundedContinuousFunction.toLp 2 C.gibbsMeasure ℝ O =
      BoundedContinuousFunction.toLp 2 C.gibbsMeasure ℝ
        (C.singleLinkHeatBathProjectionBCFOfBetaZero
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero target O)
    at hRepresentatives
  have hBCF :
      O = C.singleLinkHeatBathProjectionBCFOfBetaZero
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero target O :=
    (BoundedContinuousFunction.toLp_injective C.gibbsMeasure) hRepresentatives
  have hPointwise : C.singleLinkHeatBathProjection target O = O := by
    funext A
    exact congrArg
      (fun F : BoundedContinuousFunction C.base.Configuration ℝ => F A)
      hBCF.symm
  have hFiber : C.base.OffLinkFiberConstant target O :=
    (continuous_compact_oriented_singleLinkHeatBathProjection_fixed_iff
      C target O).mp hPointwise
  exact periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyBCF_not_offLinkFiberConstant
    hFiber

/-- The target projection annihilates the distinguished-link fluctuation. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkFluctuationL2_target_projection_eq_zero :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionL2
        periodicHypercubicThreeOriginAxisZeroTarget
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkFluctuationL2 = 0 := by
  unfold periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkFluctuationL2
  rw [continuous_compact_oriented_singleLinkHeatBathFluctuationL2_apply, map_sub,
    continuous_compact_oriented_singleLinkHeatBathProjectionL2_apply_projection,
    sub_self]

/-- Every other coordinate projection fixes the distinguished-link
fluctuation, by beta-zero pairwise commutation. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkFluctuationL2_projection_eq_self_of_ne
    (source :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hSource : source ≠ periodicHypercubicThreeOriginAxisZeroTarget) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionL2
        source periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkFluctuationL2 =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkFluctuationL2 := by
  let C := periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
  let target := periodicHypercubicThreeOriginAxisZeroTarget
  let f := C.gibbsL2RepresentativeBCF
    periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyBCF
  change C.singleLinkHeatBathProjectionL2 source
      (f - C.singleLinkHeatBathProjectionL2 target f) =
    f - C.singleLinkHeatBathProjectionL2 target f
  rw [map_sub,
    periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyL2_projection_eq_self_of_ne
      source hSource,
    ← continuous_compact_oriented_singleLinkHeatBathProjectionL2_pairwise_comm_of_beta_eq_zero
      C periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
      target source f,
    periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyL2_projection_eq_self_of_ne
      source hSource]

/-- The target fluctuation projection fixes the distinguished-link
fluctuation. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkFluctuationL2_target_fluctuation_eq_self :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
        periodicHypercubicThreeOriginAxisZeroTarget
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkFluctuationL2 =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkFluctuationL2 := by
  exact continuous_compact_oriented_singleLinkHeatBathFluctuationL2_apply_fluctuation
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
    periodicHypercubicThreeOriginAxisZeroTarget _

/-- Every other fluctuation projection annihilates the distinguished-link
fluctuation. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkFluctuationL2_fluctuation_eq_zero_of_ne
    (source :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hSource : source ≠ periodicHypercubicThreeOriginAxisZeroTarget) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
        source periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkFluctuationL2 = 0 := by
  rw [continuous_compact_oriented_singleLinkHeatBathFluctuationL2_apply,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkFluctuationL2_projection_eq_self_of_ne
      source hSource,
    sub_self]

/-- The actual beta-zero heat-bath Hamiltonian has the one-link fluctuation as
an eigenvector with eigenvalue one. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkFluctuationL2_hamiltonian_eq_self :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkFluctuationL2 =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkFluctuationL2 := by
  classical
  rw [continuous_compact_oriented_heatBathHamiltonianL2_apply]
  calc
    (∑ source :
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge,
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
        source periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkFluctuationL2) =
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
        periodicHypercubicThreeOriginAxisZeroTarget
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkFluctuationL2 := by
          apply Finset.sum_eq_single periodicHypercubicThreeOriginAxisZeroTarget
          · intro source _hSource hNe
            exact
              periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkFluctuationL2_fluctuation_eq_zero_of_ne
                source hNe
          · intro hNot
            exact (hNot (Finset.mem_univ _)).elim
    _ = periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkFluctuationL2 :=
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkFluctuationL2_target_fluctuation_eq_self

/-- The one-link fluctuation is orthogonal to the normalized Gibbs vacuum. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkFluctuationL2_inner_vacuum_eq_zero :
    inner ℝ periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkFluctuationL2 = 0 := by
  let C := periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
  let target := periodicHypercubicThreeOriginAxisZeroTarget
  let f := C.gibbsL2RepresentativeBCF
    periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyBCF
  have hSymm :=
    continuous_compact_oriented_singleLinkHeatBathFluctuationL2_inner_symm
      C target C.gibbsVacuumL2 f
  have hVacuum :
      C.singleLinkHeatBathFluctuationL2 target C.gibbsVacuumL2 = 0 := by
    rw [continuous_compact_oriented_singleLinkHeatBathFluctuationL2_apply,
      continuous_compact_oriented_singleLinkHeatBathProjectionL2_vacuum,
      sub_self]
  rw [hVacuum, inner_zero_left] at hSymm
  exact hSymm.symm

/-- Normalize the nonzero one-link fluctuation to a unit eigenvector. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2 :
    Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure :=
  ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkFluctuationL2‖⁻¹ •
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkFluctuationL2

/-- The normalized one-link vector has norm one. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2_norm_eq_one :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2‖ = 1 := by
  have hNormPos :
      0 < ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkFluctuationL2‖ :=
    norm_pos_iff.mpr
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkFluctuationL2_ne_zero
  rw [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2,
    norm_smul, norm_inv, Real.norm_of_nonneg (norm_nonneg _),
    inv_mul_cancel₀ (ne_of_gt hNormPos)]

/-- The normalized one-link vector lies in the Gibbs-vacuum orthogonal sector. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2_mem_vacuumOrthogonal :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2 ∈
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.VacuumOrthogonalL2 := by
  rw [continuous_compact_oriented_mem_vacuumOrthogonalL2_iff]
  unfold periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2
  rw [real_inner_smul_right,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkFluctuationL2_inner_vacuum_eq_zero,
    mul_zero]

/-- The normalized one-link vector remains an eigenvector with eigenvalue one. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2_hamiltonian_eq_self :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2 =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2 := by
  unfold periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2
  rw [map_smul,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkFluctuationL2_hamiltonian_eq_self]

/-- The normalized one-link eigenvector realizes Hamiltonian energy exactly
one. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2_energy_eq_one :
    inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2)
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2 = 1 := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2_hamiltonian_eq_self,
    real_inner_self_eq_norm_sq,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2_norm_eq_one]
  norm_num

/-- Energy one is realized in the actual unit vacuum-orthogonal Rayleigh set. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZero_one_mem_rayleighEnergySet :
    (1 : ℝ) ∈
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitRayleighEnergySet := by
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2_mem_vacuumOrthogonal,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2_norm_eq_one,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2_energy_eq_one⟩

/-- The actual beta-zero variational lower edge is at most one. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_rayleighInfimum_le_one :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitRayleighInfimum ≤ 1 :=
  continuous_compact_oriented_periodicVacuumOrthogonalUnitRayleighInfimum_le
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
    periodicHypercubicThreeSpecialUnitaryTwoBetaZero_one_mem_rayleighEnergySet

/-- Combining the attained upper bound with Poincare constant one identifies the
actual beta-zero variational lower edge exactly. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_rayleighInfimum_eq_one :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitRayleighInfimum = 1 := by
  exact le_antisymm
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_rayleighInfimum_le_one
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_one_le_rayleighInfimum

/-- The unit one-link eigenvector attains the variational infimum. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2_attains_rayleighInfimum :
    inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2)
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2 =
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitRayleighInfimum := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2_energy_eq_one,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_rayleighInfimum_eq_one]

/-- Compact receipt for exact finite-volume beta-zero lower-edge attainment.
This establishes a genuine eigenvector at eigenvalue one and exact attainment of
the variational lower edge, but makes no volume-uniform, nonzero-coupling, or
continuum claim. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRayleighInfimumAttainmentReceipt : Prop :=
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitRayleighInfimum = 1 ∧
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2 ∈
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.VacuumOrthogonalL2 ∧
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2‖ = 1 ∧
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2 =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2

/-- The actual beta-zero lower-edge attainment receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRayleighInfimumAttainmentReceipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRayleighInfimumAttainmentReceipt := by
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_rayleighInfimum_eq_one,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2_mem_vacuumOrthogonal,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2_norm_eq_one,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2_hamiltonian_eq_self⟩

end

end MathlibAnalytic
end MGAP4D
