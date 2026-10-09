import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPhysicalHilbertLinkBudgetBridge
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateMarginalGeometry
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# P4-Q2-C: exact original-Wilson inverse-vacuum L² cancellation

The canonical continuous strictly positive physical vacuum Omega_beta,
not an arbitrarily chosen L² representative, satisfies
  d mu_vac = Omega_beta(B)^2 d mu_Haar.
The ACTUAL original Wilson joint measure has precisely mu_vac as its
right-boundary pushforward.

Consequently the volume-independent exact equality is

  int (Omega_beta(B)^(-1))^2 d mu_joint(A,B) = 1.

This uses no compact-minimum/supremum estimate and no replacement law:
the integrand is the square of the actual reciprocal continuous vacuum.
This is a bona fide joint-L² result, not a Q2-C link-sum bound.
No claim of volume-uniform source-to-receiver norm, Gram operator norm,
Dobrushin estimate, or continuum mass gap is made.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 750000

local instance p4InverseJointTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4InverseJointCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4InverseJointSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4InverseJointMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4InverseJointBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4InverseJointLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- The reciprocal of the ACTUAL continuous positive physical vacuum
has exact squared integral 1 with respect to the existing vacuum
probability measure. The original Haar-L² vacuum representative occurs
only in the density of the existing law, and is identified a.e. with
the canonical continuous representative before cancellation. -/
theorem normalizedPhysicalOneSlabContinuousVacuumInverse_sq_integral_vacuum_eq_one
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    (∫ B,
       (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta B)⁻¹ ^ 2
       ∂(periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
         H N hN beta hbeta)) = 1 := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let Ω :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
      H N hN beta hbeta
  let old : Lp ℝ 2 μ :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
      H N hN beta hbeta).1
  let ρ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ENNReal :=
    fun B => ENNReal.ofReal ((old B) ^ 2)
  have hρMeas : AEMeasurable ρ μ :=
    ((Lp.aestronglyMeasurable old).pow 2).aemeasurable.ennreal_ofReal
  have hρTop : ∀ᵐ B ∂μ, ρ B < (⊤ : ENNReal) := by
    filter_upwards with B
    simp [ρ]
  have hΩAE : Ω =ᵐ[μ] fun B => old B := by
    simpa [Ω, old, μ] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_ae_eq_existing
        H N hN beta hbeta)
  have hΩPos : ∀ B, 0 < Ω B := fun B =>
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H N hN beta hbeta B
  change (∫ B, (Ω B)⁻¹ ^ 2 ∂(μ.withDensity ρ)) = 1
  calc
    (∫ B, (Ω B)⁻¹ ^ 2 ∂(μ.withDensity ρ)) =
        ∫ B, (ρ B).toReal • ((Ω B)⁻¹ ^ 2) ∂μ :=
      integral_withDensity_eq_integral_toReal_smul₀ hρMeas hρTop _
    _ = ∫ _B, (1 : ℝ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hΩAE] with B hB
      have hne : Ω B ≠ 0 := (hΩPos B).ne'
      simp only [smul_eq_mul]
      dsimp [ρ]
      rw [← hB, ENNReal.toReal_ofReal (sq_nonneg (Ω B))]
      field_simp [hne]
    _ = 1 := by
      haveI : IsProbabilityMeasure μ := by
        dsimp [μ, periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
        infer_instance
      simp

/-- The original Wilson joint right marginal is exactly the physical
vacuum law, so inverse-vacuum squared cancellation remains exact after
pullback onto the genuine ordered (source,right-boundary) joint carrier. -/
theorem normalizedPhysicalOneSlabContinuousVacuumInverse_sq_integral_joint_eq_one
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    (∫ z,
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H N hN beta hbeta z.2)⁻¹ ^ 2
      ∂(periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta)) = 1 := by
  let ν :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
      H N hN beta hbeta
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
      H N hN beta hbeta
  let Ω :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
      H N hN beta hbeta
  let V := normalizedPhysicalOneSlabContinuousVacuumInverseBCF
    H N hN beta hbeta
  let f := fun B => (Ω B)⁻¹ ^ 2
  have hMeas : AEStronglyMeasurable f μ := by
    have hV : Continuous (fun B => (Ω B)⁻¹) := by
      change Continuous (fun B => V B)
      exact V.continuous
    exact (hV.pow 2).aestronglyMeasurable
  have hMap : Measure.map Prod.snd ν = μ := by
    simpa [ν, μ] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_map_snd
        H N hN beta hbeta)
  change (∫ z, f z.2 ∂ν) = 1
  calc
    (∫ z, f z.2 ∂ν) =
        ∫ B, f B ∂Measure.map Prod.snd ν := by
      simpa only [Function.comp_def] using
        (MeasureTheory.integral_map
          (measurable_snd : Measurable
            (fun z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N => z.2)).aemeasurable
          (by rw [hMap]; exact hMeas)).symm
    _ = ∫ B, f B ∂μ := by rw [hMap]
    _ = 1 :=
      normalizedPhysicalOneSlabContinuousVacuumInverse_sq_integral_vacuum_eq_one
        H N hN beta hbeta

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
