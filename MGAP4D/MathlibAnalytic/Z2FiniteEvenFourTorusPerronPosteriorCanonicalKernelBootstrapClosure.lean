import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPerronPosteriorSharedPlaquetteKernel
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugePerronSmoothedPosteriorReciprocalBootstrapClosure
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance finiteEvenFourTorusSpatialLinkNonempty (H : ℕ) :
    Nonempty (FiniteEvenFourTorusSpatialLink H) :=
  ⟨(⟨0, by simp⟩, ⟨1, by norm_num⟩)⟩

/-- Canonical finite kernel bootstrap.  Stage zero is the universal full-`L¹`
top kernel; every successor is the exact finite-response bootstrap map. -/
noncomputable def finiteEvenFourTorusZ2PerronPosteriorCanonicalKernelBootstrap
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (responseIterations : ℕ) :
    ℕ →
      FiniteNonnegativeInfluenceKernelData
        (FiniteEvenFourTorusSpatialLink H)
  | 0 => finiteUniversalTwoInfluenceKernel
      (FiniteEvenFourTorusSpatialLink H)
  | stage + 1 =>
      finiteEvenFourTorusZ2PerronPosteriorKernelBootstrapNext
        H β energyIdentity energyNontrivial hβ hEnergy
        (finiteEvenFourTorusZ2PerronPosteriorCanonicalKernelBootstrap
          H β energyIdentity energyNontrivial hβ hEnergy
          responseIterations stage)
        responseIterations

@[simp] theorem finiteEvenFourTorusZ2PerronPosteriorCanonicalKernelBootstrap_zero
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (responseIterations : ℕ) :
    finiteEvenFourTorusZ2PerronPosteriorCanonicalKernelBootstrap
        H β energyIdentity energyNontrivial hβ hEnergy
        responseIterations 0 =
      finiteUniversalTwoInfluenceKernel
        (FiniteEvenFourTorusSpatialLink H) :=
  rfl

@[simp] theorem finiteEvenFourTorusZ2PerronPosteriorCanonicalKernelBootstrap_succ
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (responseIterations stage : ℕ) :
    finiteEvenFourTorusZ2PerronPosteriorCanonicalKernelBootstrap
        H β energyIdentity energyNontrivial hβ hEnergy
        responseIterations (stage + 1) =
      finiteEvenFourTorusZ2PerronPosteriorKernelBootstrapNext
        H β energyIdentity energyNontrivial hβ hEnergy
        (finiteEvenFourTorusZ2PerronPosteriorCanonicalKernelBootstrap
          H β energyIdentity energyNontrivial hβ hEnergy
          responseIterations stage)
        responseIterations :=
  rfl

/-- Every stage of the canonical bootstrap dominates all actual target-fiber
canonical non-strict influence matrices. -/
theorem finiteEvenFourTorusZ2PerronPosteriorCanonicalKernelBootstrap_dominates
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (responseIterations stage : ℕ) :
    FiniteEvenFourTorusZ2PerronPosteriorCanonicalDominatedBy
      H β energyIdentity energyNontrivial hβ hEnergy
      (finiteEvenFourTorusZ2PerronPosteriorCanonicalKernelBootstrap
        H β energyIdentity energyNontrivial hβ hEnergy
        responseIterations stage) := by
  induction stage with
  | zero =>
      intro environment boundaryTarget g target source
      exact
        finitePositiveWeightCanonicalNonstrictInfluence_le_universalTwoKernel
          (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
            H β energyIdentity energyNontrivial hβ.le hEnergy.le
            (Function.update environment boundaryTarget g))
          (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight_pos
            H β energyIdentity energyNontrivial hβ hEnergy
            (Function.update environment boundaryTarget g))
          target source
  | succ stage ih =>
      rw [
        finiteEvenFourTorusZ2PerronPosteriorCanonicalKernelBootstrap_succ]
      exact
        finiteEvenFourTorusZ2PerronPosteriorCanonicalDominatedBy_next
          H β energyIdentity energyNontrivial hβ hEnergy
          (finiteEvenFourTorusZ2PerronPosteriorCanonicalKernelBootstrap
            H β energyIdentity energyNontrivial hβ hEnergy
            responseIterations stage)
          responseIterations ih

/-- Exact maximum column coefficient at one canonical bootstrap stage. -/
noncomputable def finiteEvenFourTorusZ2PerronPosteriorBootstrapColumnCoefficient
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (responseIterations stage : ℕ) : ℝ :=
  finiteInfluenceKernelMaximumColumnSum
    (finiteEvenFourTorusZ2PerronPosteriorCanonicalKernelBootstrap
      H β energyIdentity energyNontrivial hβ hEnergy
      responseIterations stage)

/-- The exact bootstrap column coefficient is nonnegative. -/
theorem finiteEvenFourTorusZ2PerronPosteriorBootstrapColumnCoefficient_nonneg
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (responseIterations stage : ℕ) :
    0 ≤ finiteEvenFourTorusZ2PerronPosteriorBootstrapColumnCoefficient
      H β energyIdentity energyNontrivial hβ hEnergy
      responseIterations stage := by
  unfold finiteEvenFourTorusZ2PerronPosteriorBootstrapColumnCoefficient
  exact finiteInfluenceKernelMaximumColumnSum_nonneg _

/-- Every column at a canonical stage is bounded by its exact maximum. -/
theorem finiteEvenFourTorusZ2PerronPosteriorBootstrapColumnSum_le
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (responseIterations stage : ℕ)
    (source : FiniteEvenFourTorusSpatialLink H) :
    finiteInfluenceKernelColumnSum
        (finiteEvenFourTorusZ2PerronPosteriorCanonicalKernelBootstrap
          H β energyIdentity energyNontrivial hβ hEnergy
          responseIterations stage)
        source ≤
      finiteEvenFourTorusZ2PerronPosteriorBootstrapColumnCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy
        responseIterations stage :=
  finiteInfluenceKernelColumnSum_le_maximum _ source

/-- One-factor local coefficient used by the final reciprocal row closure. -/
def finiteEvenFourTorusZ2PerronPosteriorLocalCoefficient
    (β energyIdentity energyNontrivial : ℝ) : ℝ :=
  48 * finiteEvenFourTorusZ2PerronPosteriorLocalInfluenceMajorant
    β energyIdentity energyNontrivial

/-- The local coefficient is nonnegative. -/
theorem finiteEvenFourTorusZ2PerronPosteriorLocalCoefficient_nonneg
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    0 ≤ finiteEvenFourTorusZ2PerronPosteriorLocalCoefficient
      β energyIdentity energyNontrivial := by
  exact mul_nonneg (by norm_num)
    (finiteEvenFourTorusZ2PerronPosteriorLocalInfluenceMajorant_nonneg
      β energyIdentity energyNontrivial hβ hEnergy)

/-- The exact local row is bounded by the explicit one-factor coefficient. -/
theorem finiteEvenFourTorusZ2PerronPosteriorLocalRowSum_le_coefficient
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (target : FiniteEvenFourTorusSpatialLink H) :
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluenceRowSum
        H β energyIdentity energyNontrivial target ≤
      finiteEvenFourTorusZ2PerronPosteriorLocalCoefficient
        β energyIdentity energyNontrivial :=
  finiteEvenFourTorusZ2PerronPosteriorLocalInfluenceRowSum_le
    H β energyIdentity energyNontrivial hβ hEnergy target

/-- The two exact local half-actions are already strict under the explicit
shared-plaquette threshold `majorant < 1/96`. -/
theorem finiteEvenFourTorusZ2PerronPosterior_twoLocalCoefficient_lt_one
    (β energyIdentity energyNontrivial : ℝ)
    (hThreshold :
      finiteEvenFourTorusZ2PerronPosteriorLocalInfluenceMajorant
        β energyIdentity energyNontrivial < (96 : ℝ)⁻¹) :
    2 * finiteEvenFourTorusZ2PerronPosteriorLocalCoefficient
        β energyIdentity energyNontrivial < 1 := by
  unfold finiteEvenFourTorusZ2PerronPosteriorLocalCoefficient
  norm_num at hThreshold ⊢
  nlinarith

/-- Explicit source-summed response coefficient associated with a stage
column coefficient. -/
noncomputable def finiteEvenFourTorusZ2PerronPosteriorBootstrapResponseCoefficient
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (responseIterations : ℕ)
    (columnCoefficient : ℝ) : ℝ :=
  let ratio :=
    finiteZ2CrossingLikelihoodRatio
      (z2WilsonTemporalCrossingRate
        β energyIdentity energyNontrivial)
  let sourceMagnitude := ratio - ratio⁻¹
  finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTiltSourceAmplitude
      β energyIdentity energyNontrivial *
      sourceMagnitude * (1 - columnCoefficient)⁻¹ +
    2 * (Fintype.card (FiniteEvenFourTorusSpatialLink H) : ℝ) *
      (finiteInfluenceKernelReciprocalRandomScanRate
        (FiniteEvenFourTorusSpatialLink H) columnCoefficient ^
          responseIterations * sourceMagnitude)

/-- Complete explicit scalar tested at one finite canonical bootstrap stage. -/
noncomputable def finiteEvenFourTorusZ2PerronPosteriorBootstrapClosureCoefficient
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (responseIterations stage : ℕ) : ℝ :=
  2 * finiteEvenFourTorusZ2PerronPosteriorLocalCoefficient
        β energyIdentity energyNontrivial +
    finiteZ2CrossingLikelihoodRatio
        (z2WilsonTemporalCrossingRate
          β energyIdentity energyNontrivial) *
      finiteEvenFourTorusZ2PerronPosteriorBootstrapResponseCoefficient
        H β energyIdentity energyNontrivial responseIterations
        (finiteEvenFourTorusZ2PerronPosteriorBootstrapColumnCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy
          responseIterations stage)

/-- A finite, fully canonical high-temperature witness.  No arbitrary kernel
and no assumed target-fiber Dobrushin matrix occurs among its fields. -/
structure Z2PerronPosteriorFiniteBootstrapHighTemperatureCertificate
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) where
  responseIterations : ℕ
  stage : ℕ
  columnCoefficient_lt_one :
    finiteEvenFourTorusZ2PerronPosteriorBootstrapColumnCoefficient
      H β energyIdentity energyNontrivial hβ hEnergy
      responseIterations stage < 1
  closureCoefficient_lt_one :
    finiteEvenFourTorusZ2PerronPosteriorBootstrapClosureCoefficient
      H β energyIdentity energyNontrivial hβ hEnergy
      responseIterations stage < 1

namespace Z2PerronPosteriorFiniteBootstrapHighTemperatureCertificate

variable
    {H : ℕ}
    {β energyIdentity energyNontrivial : ℝ}
    {hβ : 0 < β}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorFiniteBootstrapHighTemperatureCertificate
      H β energyIdentity energyNontrivial hβ hEnergy)

/-- The canonical strict reciprocal-kernel certificate at the witnessed
bootstrap stage. -/
noncomputable def reciprocal :
    FiniteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorReciprocalKernelCertificate
      H β energyIdentity energyNontrivial hβ hEnergy :=
  { iterations := C.responseIterations
    kernel :=
      finiteEvenFourTorusZ2PerronPosteriorCanonicalKernelBootstrap
        H β energyIdentity energyNontrivial hβ hEnergy
        C.responseIterations C.stage
    columnCoefficient :=
      finiteEvenFourTorusZ2PerronPosteriorBootstrapColumnCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy
        C.responseIterations C.stage
    columnCoefficient_nonneg :=
      finiteEvenFourTorusZ2PerronPosteriorBootstrapColumnCoefficient_nonneg
        H β energyIdentity energyNontrivial hβ hEnergy
        C.responseIterations C.stage
    columnCoefficient_lt_one := C.columnCoefficient_lt_one
    columnSum_le :=
      finiteEvenFourTorusZ2PerronPosteriorBootstrapColumnSum_le
        H β energyIdentity energyNontrivial hβ hEnergy
        C.responseIterations C.stage
    canonicalInfluence_le :=
      finiteEvenFourTorusZ2PerronPosteriorCanonicalKernelBootstrap_dominates
        H β energyIdentity energyNontrivial hβ hEnergy
        C.responseIterations C.stage }

/-- The existing reciprocal response coefficient is definitionally the
explicit scalar recorded by the canonical stage. -/
theorem reciprocal_responseRowCoefficient :
    C.reciprocal.responseRowCoefficient =
      finiteEvenFourTorusZ2PerronPosteriorBootstrapResponseCoefficient
        H β energyIdentity energyNontrivial C.responseIterations
        (finiteEvenFourTorusZ2PerronPosteriorBootstrapColumnCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy
          C.responseIterations C.stage) := by
  rfl

/-- The finite bootstrap witness generates the final non-circular reciprocal
closure certificate. -/
noncomputable def closure :
    FiniteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorReciprocalClosureCertificate
      H β energyIdentity energyNontrivial hβ hEnergy :=
  { reciprocal := C.reciprocal
    localCoefficient :=
      finiteEvenFourTorusZ2PerronPosteriorLocalCoefficient
        β energyIdentity energyNontrivial
    localCoefficient_nonneg :=
      finiteEvenFourTorusZ2PerronPosteriorLocalCoefficient_nonneg
        β energyIdentity energyNontrivial hβ.le hEnergy.le
    localRowSum_le :=
      finiteEvenFourTorusZ2PerronPosteriorLocalRowSum_le_coefficient
        H β energyIdentity energyNontrivial hβ.le hEnergy.le
    coefficient_lt_one := by
      rw [C.reciprocal_responseRowCoefficient]
      exact C.closureCoefficient_lt_one }

/-- Actual strict target-fiber Dobrushin data generated from the canonical
finite bootstrap stage. -/
noncomputable def toDobrushinData
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H) :
    FinitePositiveWeightDobrushinL1MatrixData
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
        H β energyIdentity energyNontrivial hβ.le hEnergy.le environment) :=
  C.closure.toDobrushinData environment

end Z2PerronPosteriorFiniteBootstrapHighTemperatureCertificate

/-- All-volume version of the finite canonical bootstrap criterion.  The stage
and response depth may depend on the finite side, while the formulas and
strict threshold are fixed and fully explicit. -/
structure Z2PerronPosteriorFiniteBootstrapHighTemperatureFamilyCertificate
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) where
  atVolume :
    ∀ H : ℕ,
      Z2PerronPosteriorFiniteBootstrapHighTemperatureCertificate
        H β energyIdentity energyNontrivial hβ hEnergy

/-- The all-volume canonical bootstrap certificate supplies actual strict
posterior Dobrushin matrices at every finite side and every environment. -/
noncomputable def
    Z2PerronPosteriorFiniteBootstrapHighTemperatureFamilyCertificate.toDobrushinData
    {β energyIdentity energyNontrivial : ℝ}
    {hβ : 0 < β}
    {hEnergy : energyIdentity < energyNontrivial}
    (C :
      Z2PerronPosteriorFiniteBootstrapHighTemperatureFamilyCertificate
        β energyIdentity energyNontrivial hβ hEnergy)
    (H : ℕ)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H) :
    FinitePositiveWeightDobrushinL1MatrixData
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
        H β energyIdentity energyNontrivial hβ.le hEnergy.le environment) :=
  (C.atVolume H).toDobrushinData environment

end

end MathlibAnalytic
end MGAP4D
