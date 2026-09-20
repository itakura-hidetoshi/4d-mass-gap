import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceRemoteConditionalCrossRatioInfluence
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceDistinctFiberRemoteSlabCancellation
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceOffTargetHeatBathRawVacuumDoobBridge
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance distinguishedTargetRemoteCrossRatioSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance distinguishedTargetRemoteCrossRatioSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance distinguishedTargetRemoteCrossRatioSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance distinguishedTargetRemoteCrossRatioSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance distinguishedTargetRemoteCrossRatioSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberENNRealWeight_mass_eq_ofReal_partitionFunction
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target referenceSource fiber :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    doobWeightMass
        (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
        (fun g =>
          ENNReal.ofReal
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
              H N hN beta hbeta B target referenceSource fiber k g₂ A g)) =
      ENNReal.ofReal
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberPartitionFunction
          H N hN beta hbeta B target referenceSource fiber k g₂ A) := by
  let μ := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let w :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
      H N hN beta hbeta B target referenceSource fiber k g₂ A
  have hwInt : Integrable w μ := by
    simpa [μ, w] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight_integrable
        H N hN beta hbeta B target referenceSource fiber k g₂ A
  have hwNonneg : ∀ᵐ g ∂μ, 0 ≤ w g := by
    exact ae_of_all μ fun g =>
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight_pos
        H N hN beta hbeta B target referenceSource fiber k g₂ A g).le
  unfold doobWeightMass
  change (∫⁻ g, ENNReal.ofReal (w g) ∂μ) =
    ENNReal.ofReal (∫ g, w g ∂μ)
  exact (ofReal_integral_eq_lintegral_ofReal hwInt hwNonneg).symm

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_distinguishedTarget_remote_boundedTest_difference_le_worstCaseCrossRatioInfluenceMajorant
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedTarget distinguishedSource backgroundSource :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : distinguishedTarget ≠ backgroundSource)
    (hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette
        H distinguishedTarget backgroundSource)
    (k g₂ u v : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (phi : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (hphi : StronglyMeasurable phi)
    (hphiBound : ∀ g, |phi g| ≤ 1) :
    |(∫ g, phi g
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B distinguishedTarget distinguishedSource
          distinguishedTarget k g₂ (Function.update A backgroundSource u)) -
      (∫ g, phi g
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B distinguishedTarget distinguishedSource
          distinguishedTarget k g₂ (Function.update A backgroundSource v))| ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseCrossRatioInfluenceMajorant
        H N hN beta hbeta A distinguishedTarget backgroundSource := by
  classical
  let μ : Measure (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let wuReal :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
      H N hN beta hbeta B distinguishedTarget distinguishedSource
      distinguishedTarget k g₂ (Function.update A backgroundSource u)
  let wvReal :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
      H N hN beta hbeta B distinguishedTarget distinguishedSource
      distinguishedTarget k g₂ (Function.update A backgroundSource v)
  let wu : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ≥0∞ :=
    fun g => ENNReal.ofReal (wuReal g)
  let wv : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ≥0∞ :=
    fun g => ENNReal.ofReal (wvReal g)
  let radius :
      Matrix.specialUnitaryGroup (Fin N) ℂ →
      Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ :=
    fun x y =>
      Real.log
        (1 + Real.exp (16 * beta) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs
            H N hN beta hbeta A distinguishedTarget backgroundSource x y u v)
  let M : ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseCrossRatioInfluenceMajorant
      H N hN beta hbeta A distinguishedTarget backgroundSource
  have hMNonneg : 0 ≤ M := by
    have hChosenNonneg :
        0 ≤
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioCrossRatioInfluenceMajorant
            H N hN beta hbeta A distinguishedTarget backgroundSource 1 1 1 1 := by
      unfold
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioCrossRatioInfluenceMajorant
      exact
        finitePositiveWeightCrossRatioInfluenceTransform_nonneg _
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioCrossRatioRadius_nonneg
            H N hN beta hbeta A distinguishedTarget backgroundSource 1 1 1 1)
    have hChosenLe :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioCrossRatioInfluenceMajorant_le_worstCase
        H N hN beta hbeta A distinguishedTarget backgroundSource 1 1 1 1
    exact hChosenNonneg.trans (by simpa [M] using hChosenLe)
  have hMLeTwo : M ≤ 2 := by
    dsimp [M]
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseCrossRatioInfluenceMajorant
    apply csSup_le
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioCrossRatioInfluenceMajorantSet_nonempty
        H N hN beta hbeta A distinguishedTarget backgroundSource)
    intro x hx
    rcases hx with ⟨g₁, g₂', h, k', rfl⟩
    exact
      (finitePositiveWeightCrossRatioInfluenceTransform_lt_two
        (Real.log
          (1 + Real.exp (16 * beta) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs
              H N hN beta hbeta A distinguishedTarget backgroundSource
              g₁ g₂' h k'))).le
  have hRadiusNonneg : ∀ x y, 0 ≤ radius x y := by
    intro x y
    simpa [radius] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioCrossRatioRadius_nonneg
        H N hN beta hbeta A distinguishedTarget backgroundSource x y u v
  have hInfluence : ∀ x y,
      finitePositiveWeightCrossRatioInfluenceTransform (radius x y) ≤ M := by
    intro x y
    simpa [
      radius,
      M,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioCrossRatioInfluenceMajorant] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioCrossRatioInfluenceMajorant_le_worstCase
        H N hN beta hbeta A distinguishedTarget backgroundSource x y u v
  have hwutop : ∀ x, wu x ≠ ∞ := by
    intro x
    exact ENNReal.ofReal_ne_top
  have hwvtop : ∀ x, wv x ≠ ∞ := by
    intro x
    exact ENNReal.ofReal_ne_top
  have hMassU :
      doobWeightMass μ wu =
        ENNReal.ofReal
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberPartitionFunction
            H N hN beta hbeta B distinguishedTarget distinguishedSource
            distinguishedTarget k g₂ (Function.update A backgroundSource u)) := by
    simpa [μ, wu, wuReal] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberENNRealWeight_mass_eq_ofReal_partitionFunction
        H N hN beta hbeta B distinguishedTarget distinguishedSource
        distinguishedTarget k g₂ (Function.update A backgroundSource u)
  have hMassV :
      doobWeightMass μ wv =
        ENNReal.ofReal
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberPartitionFunction
            H N hN beta hbeta B distinguishedTarget distinguishedSource
            distinguishedTarget k g₂ (Function.update A backgroundSource v)) := by
    simpa [μ, wv, wvReal] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberENNRealWeight_mass_eq_ofReal_partitionFunction
        H N hN beta hbeta B distinguishedTarget distinguishedSource
        distinguishedTarget k g₂ (Function.update A backgroundSource v)
  have hMassUPos :
      0 <
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberPartitionFunction
          H N hN beta hbeta B distinguishedTarget distinguishedSource
          distinguishedTarget k g₂ (Function.update A backgroundSource u) :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberPartitionFunction_pos
      H N hN beta hbeta B distinguishedTarget distinguishedSource
      distinguishedTarget k g₂ (Function.update A backgroundSource u)
  have hMassVPos :
      0 <
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberPartitionFunction
          H N hN beta hbeta B distinguishedTarget distinguishedSource
          distinguishedTarget k g₂ (Function.update A backgroundSource v) :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberPartitionFunction_pos
      H N hN beta hbeta B distinguishedTarget distinguishedSource
      distinguishedTarget k g₂ (Function.update A backgroundSource v)
  have hMassU0 : doobWeightMass μ wu ≠ 0 := by
    rw [hMassU]
    exact ENNReal.ofReal_ne_zero.mpr hMassUPos.ne'
  have hMassV0 : doobWeightMass μ wv ≠ 0 := by
    rw [hMassV]
    exact ENNReal.ofReal_ne_zero.mpr hMassVPos.ne'
  have hMassUtop : doobWeightMass μ wu ≠ ∞ := by
    rw [hMassU]
    exact ENNReal.ofReal_ne_top
  have hMassVtop : doobWeightMass μ wv ≠ ∞ := by
    rw [hMassV]
    exact ENNReal.ofReal_ne_top
  have hcross : ∀ x y,
      wu x * wv y ≤
        ENNReal.ofReal (Real.exp (radius x y)) * wv x * wu y := by
    intro x y
    let Ux := Function.update (Function.update A backgroundSource u) distinguishedTarget x
    let Uy := Function.update (Function.update A backgroundSource u) distinguishedTarget y
    let Vx := Function.update (Function.update A backgroundSource v) distinguishedTarget x
    let Vy := Function.update (Function.update A backgroundSource v) distinguishedTarget y
    let Ax := Function.update A distinguishedTarget x
    let Ay := Function.update A distinguishedTarget y
    let omega :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H N hN beta hbeta
    let targetLocal :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
        H N beta
    let slab :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N beta
    let Br := Function.update B distinguishedSource k
    have hCommUx : Ux = Function.update Ax backgroundSource u := by
      funext e
      by_cases heTarget : e = distinguishedTarget
      · subst e
        simp [Ux, Ax, hne, Ne.symm hne]
      · by_cases heBackground : e = backgroundSource
        · subst e
          simp [Ux, Ax, hne, Ne.symm hne]
        · simp [Ux, Ax, heTarget, heBackground]
    have hCommVx : Vx = Function.update Ax backgroundSource v := by
      funext e
      by_cases heTarget : e = distinguishedTarget
      · subst e
        simp [Vx, Ax, hne, Ne.symm hne]
      · by_cases heBackground : e = backgroundSource
        · subst e
          simp [Vx, Ax, hne, Ne.symm hne]
        · simp [Vx, Ax, heTarget, heBackground]
    have hCommUy : Uy = Function.update Ay backgroundSource u := by
      funext e
      by_cases heTarget : e = distinguishedTarget
      · subst e
        simp [Uy, Ay, hne, Ne.symm hne]
      · by_cases heBackground : e = backgroundSource
        · subst e
          simp [Uy, Ay, hne, Ne.symm hne]
        · simp [Uy, Ay, heTarget, heBackground]
    have hCommVy : Vy = Function.update Ay backgroundSource v := by
      funext e
      by_cases heTarget : e = distinguishedTarget
      · subst e
        simp [Vy, Ay, hne, Ne.symm hne]
      · by_cases heBackground : e = backgroundSource
        · subst e
          simp [Vy, Ay, hne, Ne.symm hne]
        · simp [Vy, Ay, heTarget, heBackground]
    have hLocalUx :
        targetLocal Ux B distinguishedTarget g₂ =
          targetLocal Ax B distinguishedTarget g₂ := by
      rw [hCommUx]
      exact
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_update_left_of_ne
          H N beta Ax B distinguishedTarget backgroundSource u g₂ (Ne.symm hne)
    have hLocalVx :
        targetLocal Vx B distinguishedTarget g₂ =
          targetLocal Ax B distinguishedTarget g₂ := by
      rw [hCommVx]
      exact
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_update_left_of_ne
          H N beta Ax B distinguishedTarget backgroundSource v g₂ (Ne.symm hne)
    have hLocalUy :
        targetLocal Uy B distinguishedTarget g₂ =
          targetLocal Ay B distinguishedTarget g₂ := by
      rw [hCommUy]
      exact
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_update_left_of_ne
          H N beta Ay B distinguishedTarget backgroundSource u g₂ (Ne.symm hne)
    have hLocalVy :
        targetLocal Vy B distinguishedTarget g₂ =
          targetLocal Ay B distinguishedTarget g₂ := by
      rw [hCommVy]
      exact
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_update_left_of_ne
          H N beta Ay B distinguishedTarget backgroundSource v g₂ (Ne.symm hne)
    have hSlabCrossRaw :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_remote_background_crossRatio_eq
        H N beta Br A backgroundSource distinguishedTarget u v x y
        (Ne.symm hne) hNoShare
    have hSlabCross :
        slab Ux Br * slab Vy Br = slab Vx Br * slab Uy Br := by
      dsimp [slab]
      rw [
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_symmetric
          H N hN beta hbeta Ux Br,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_symmetric
          H N hN beta hbeta Vy Br,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_symmetric
          H N hN beta hbeta Vx Br,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_symmetric
          H N hN beta hbeta Uy Br]
      calc
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta Br Ux *
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta Br Vy =
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta Br Uy *
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta Br Vx := by
              simpa [Ux, Uy, Vx, Vy, Br] using hSlabCrossRaw
        _ =
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta Br Vx *
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta Br Uy := by
              exact mul_comm _ _
    have hVacRatio :
        omega Ux * omega Vy /
            (omega Vx * omega Uy) ≤
          Real.exp (radius x y) := by
      simpa [Ux, Uy, Vx, Vy, omega, radius] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_remote_crossRatio_le_exp_log_one_add_exp_sixteen_mul_fixedRightTargetRatioResponseAbs
          H N hN beta hbeta A hne hNoShare u v x y
    have hVacDen : 0 < omega Vx * omega Uy := by
      exact mul_pos
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
          H N hN beta hbeta Vx)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
          H N hN beta hbeta Uy)
    have hVacMul :
        omega Ux * omega Vy ≤
          Real.exp (radius x y) * (omega Vx * omega Uy) :=
      (div_le_iff₀ hVacDen).mp hVacRatio
    have hCommonNonneg :
        0 ≤
          (targetLocal Ux B distinguishedTarget g₂ *
            targetLocal Vy B distinguishedTarget g₂) *
          (slab Ux Br * slab Vy Br) := by
      exact mul_nonneg
        (mul_nonneg
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_pos
            H N beta Ux B distinguishedTarget g₂).le
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_pos
            H N beta Vy B distinguishedTarget g₂).le)
        (mul_nonneg
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
            H N beta Ux Br).le
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
            H N beta Vy Br).le)
    have hCommonEq :
        (targetLocal Ux B distinguishedTarget g₂ *
            targetLocal Vy B distinguishedTarget g₂) *
          (slab Ux Br * slab Vy Br) =
        (targetLocal Vx B distinguishedTarget g₂ *
            targetLocal Uy B distinguishedTarget g₂) *
          (slab Vx Br * slab Uy Br) := by
      rw [hLocalUx, hLocalVx, hLocalUy, hLocalVy, hSlabCross]
    have hFullMul :
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
              H N hN beta hbeta B distinguishedTarget distinguishedSource k g₂ Ux *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
              H N hN beta hbeta B distinguishedTarget distinguishedSource k g₂ Vy ≤
          Real.exp (radius x y) *
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
                H N hN beta hbeta B distinguishedTarget distinguishedSource k g₂ Vx *
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
                H N hN beta hbeta B distinguishedTarget distinguishedSource k g₂ Uy) := by
      unfold
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
      calc
        (omega Ux * targetLocal Ux B distinguishedTarget g₂ * slab Ux Br) *
            (omega Vy * targetLocal Vy B distinguishedTarget g₂ * slab Vy Br) =
          (omega Ux * omega Vy) *
            ((targetLocal Ux B distinguishedTarget g₂ *
                targetLocal Vy B distinguishedTarget g₂) *
              (slab Ux Br * slab Vy Br)) := by ring
        _ ≤
          (Real.exp (radius x y) * (omega Vx * omega Uy)) *
            ((targetLocal Ux B distinguishedTarget g₂ *
                targetLocal Vy B distinguishedTarget g₂) *
              (slab Ux Br * slab Vy Br)) :=
          mul_le_mul_of_nonneg_right hVacMul hCommonNonneg
        _ =
          Real.exp (radius x y) *
            ((omega Vx * targetLocal Vx B distinguishedTarget g₂ * slab Vx Br) *
              (omega Uy * targetLocal Uy B distinguishedTarget g₂ * slab Uy Br)) := by
          rw [hCommonEq]
          ring
    have hUxPos :
        0 <
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
            H N hN beta hbeta B distinguishedTarget distinguishedSource k g₂ Ux :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight_pos
        H N hN beta hbeta B distinguishedTarget distinguishedSource k g₂ Ux
    have hVyPos :
        0 <
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
            H N hN beta hbeta B distinguishedTarget distinguishedSource k g₂ Vy :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight_pos
        H N hN beta hbeta B distinguishedTarget distinguishedSource k g₂ Vy
    have hVxPos :
        0 <
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
            H N hN beta hbeta B distinguishedTarget distinguishedSource k g₂ Vx :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight_pos
        H N hN beta hbeta B distinguishedTarget distinguishedSource k g₂ Vx
    have hUyPos :
        0 <
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
            H N hN beta hbeta B distinguishedTarget distinguishedSource k g₂ Uy :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight_pos
        H N hN beta hbeta B distinguishedTarget distinguishedSource k g₂ Uy
    have hENN :
        ENNReal.ofReal
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
              H N hN beta hbeta B distinguishedTarget distinguishedSource k g₂ Ux) *
          ENNReal.ofReal
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
              H N hN beta hbeta B distinguishedTarget distinguishedSource k g₂ Vy) ≤
        ENNReal.ofReal (Real.exp (radius x y)) *
          ENNReal.ofReal
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
              H N hN beta hbeta B distinguishedTarget distinguishedSource k g₂ Vx) *
          ENNReal.ofReal
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
              H N hN beta hbeta B distinguishedTarget distinguishedSource k g₂ Uy) := by
      calc
        _ =
            ENNReal.ofReal
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
                  H N hN beta hbeta B distinguishedTarget distinguishedSource k g₂ Ux *
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
                  H N hN beta hbeta B distinguishedTarget distinguishedSource k g₂ Vy) := by
              rw [ENNReal.ofReal_mul hUxPos.le]
        _ ≤
            ENNReal.ofReal
              (Real.exp (radius x y) *
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
                    H N hN beta hbeta B distinguishedTarget distinguishedSource k g₂ Vx *
                  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
                    H N hN beta hbeta B distinguishedTarget distinguishedSource k g₂ Uy)) :=
              ENNReal.ofReal_le_ofReal hFullMul
        _ =
            ENNReal.ofReal (Real.exp (radius x y)) *
              ENNReal.ofReal
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
                  H N hN beta hbeta B distinguishedTarget distinguishedSource k g₂ Vx) *
              ENNReal.ofReal
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
                  H N hN beta hbeta B distinguishedTarget distinguishedSource k g₂ Uy) := by
              rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
              rw [ENNReal.ofReal_mul hVxPos.le]
    simpa [
      wu,
      wv,
      wuReal,
      wvReal,
      Ux,
      Uy,
      Vx,
      Vy,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight,
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink] using hENN
  have hDoob :=
    doobWeightedMeasure_boundedTest_integral_difference_abs_le_crossRatioInfluenceMajorant
      μ wu wv radius M
      hMNonneg hMLeTwo hRadiusNonneg hInfluence
      hwutop hwvtop hMassU0 hMassUtop hMassV0 hMassVtop
      hcross phi hphi hphiBound
  have hEqU :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_eq_spatialLinkFiberNormalizedMeasure
      H N hN beta hbeta B distinguishedTarget distinguishedSource
      distinguishedTarget k g₂ (Function.update A backgroundSource u)
  have hEqV :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_eq_spatialLinkFiberNormalizedMeasure
      H N hN beta hbeta B distinguishedTarget distinguishedSource
      distinguishedTarget k g₂ (Function.update A backgroundSource v)
  rw [hEqU, hEqV]
  simpa [
    μ,
    wu,
    wv,
    wuReal,
    wvReal,
    M,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSpatialLinkFiberNormalizedMeasure,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSpatialLinkFiberENNRealWeight,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight,
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink] using hDoob

end

end MathlibAnalytic
end MGAP4D
