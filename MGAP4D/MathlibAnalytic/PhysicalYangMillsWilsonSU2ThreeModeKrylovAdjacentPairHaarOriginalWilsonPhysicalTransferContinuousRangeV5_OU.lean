import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonContinuousPhysicalGIDetectionV5_OT
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumRepresentative
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferNormalization
import Mathlib.Tactic

/-!
# P4-Q2-OU — true normalized Wilson physical transfer has continuous Haar-L² image

The OT true two-interacting-Wilson-posterior GI separation theorem
applies to nonzero Gauss-law Hilbert sources possessing a genuine
continuous and gauge-invariant Haar-L² representative.

Here the REGULARITY obstacle is attacked directly in the unchanged
physical Wilson theory: the actual complete full-spatial SU(2) Wilson
one-slab physical transfer is already factored A_phys† A_phys, and
the true ambient Wilson kernel's Moore--Aronszajn feature synthesis
A†v is represented by a genuine continuous spatial configuration
function for EVERY feature vector v.

Using the exact original physical operator equality (not a surrogate)
and the genuine feature-synthesis L² equivalence, we prove for EVERY
true Gauss-law input f (with no continuity assumption) that the output
of the unnormalized and normalized positive/nonnegative-fine Wilson
transfer admits a continuous original-Haar-L² representative.

This is genuine one-slab smoothing of arbitrary physical f.
Pointwise gauge invariance of the chosen representative, its
iteration to all Krylov powers and the nonvanishing of the true OO
Schur physical source remain separate gates. No Dobrushin,
independent-Haar substitute, sorry/admit, new axiom, U0 or
continuum Yang--Mills mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2OU_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2OU_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2OU_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2OU_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2OU_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

section ActualPositivePhysicalOneSlab
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2

/-- The actual FULL original Wilson one-slab physical transfer's
continuous output, obtained by synthesis in the canonical feature
Hilbert space. In contrast to the vacuum-specific earlier theorem,
the input may be ANY Gauss-law physical L² source. -/
noncomputable def p4Q2OU_originalPhysicalTransferContinuous
    (t : ℝ) (ht : 0 ≤ t) (f : Phys) : C(Cfg, ℝ) :=
  ⟨periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisFunction
      H 2 specialUnitaryTwoWilsonRankPositive t ht
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
        H 2 specialUnitaryTwoWilsonRankPositive t ht f),
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisFunction_continuous
      H 2 specialUnitaryTwoWilsonRankPositive t ht _⟩

/-- The continuous synthesis is EXACTLY the actual unnormalized
physical Wilson transfer of ANY Gauss-law Hilbert input in original
spatial Haar-L². This is the genuine physical A†A factorization. -/
theorem p4Q2OU_originalPhysicalTransferContinuous_toLp
    (t : ℝ) (ht : 0 ≤ t) (f : Phys) :
    ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H 2 specialUnitaryTwoWilsonRankPositive t ht f : Phys) :
      Lp ℝ 2 haar) =
      ContinuousMap.toLp 2 haar ℝ
        (p4Q2OU_originalPhysicalTransferContinuous H t ht f) := by
  let v :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
      H 2 specialUnitaryTwoWilsonRankPositive t ht f
  let S :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisL2
      H 2 specialUnitaryTwoWilsonRankPositive t ht v
  let ψ : C(Cfg, ℝ) := p4Q2OU_originalPhysicalTransferContinuous H t ht f
  have hS_transfer :
      S =
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H 2 specialUnitaryTwoWilsonRankPositive t ht
          (f : Lp ℝ 2 haar) := by
    dsimp [S, v]
    rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisL2_eq_adjoint]
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator_apply]
    rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_eq_adjoint_comp_analysis]
    rfl
  have hS_cont :
      S = ContinuousMap.toLp 2 haar ℝ ψ := by
    apply Lp.ext
    have hS :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisL2_coeFn
        H 2 specialUnitaryTwoWilsonRankPositive t ht v
    have hψ := ψ.coeFn_toLp (p := 2) (𝕜 := ℝ) haar
    exact hS.trans hψ.symm
  calc
    ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H 2 specialUnitaryTwoWilsonRankPositive t ht f : Phys) :
      Lp ℝ 2 haar) =
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H 2 specialUnitaryTwoWilsonRankPositive t ht (f : Lp ℝ 2 haar) :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_coe
        H 2 specialUnitaryTwoWilsonRankPositive t ht f
    _ = S := hS_transfer.symm
    _ = ContinuousMap.toLp 2 haar ℝ ψ := hS_cont

/-- This property survives EXACT physical norm normalization, with
the TRUE, strictly positive original transfer operator norm. -/
theorem p4Q2OU_originalNormalizedPhysicalTransferContinuous_toLp
    (t : ℝ) (ht : 0 ≤ t) (f : Phys) :
    ((periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          H 2 specialUnitaryTwoWilsonRankPositive t ht f : Phys) :
      Lp ℝ 2 haar) =
      ContinuousMap.toLp 2 haar ℝ
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H 2 specialUnitaryTwoWilsonRankPositive t ht‖⁻¹ •
            p4Q2OU_originalPhysicalTransferContinuous H t ht f) := by
  have hRaw := p4Q2OU_originalPhysicalTransferContinuous_toLp H t ht f
  rw [periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_apply]
  change
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H 2 specialUnitaryTwoWilsonRankPositive t ht‖⁻¹ •
        ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H 2 specialUnitaryTwoWilsonRankPositive t ht f : Phys) : Lp ℝ 2 haar) =
      _
  rw [hRaw, map_smul]

/-- Direct result needed for the actual repeated fine Wilson
right-Krylov orbit: EVERY normalized physical image of an arbitrary
Gauss-law input (including a previous Krylov mode) possesses a
literal continuous Haar-L² representative, without a smoothness
assumption on the input. -/
theorem p4Q2OU_originalNormalizedPhysicalTransfer_hasContinuousRepresentative
    (t : ℝ) (ht : 0 ≤ t) (f : Phys) :
    ∃ ψ : C(Cfg, ℝ),
      (fun A : Cfg =>
        ((periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          H 2 specialUnitaryTwoWilsonRankPositive t ht f : Phys) :
          Lp ℝ 2 haar) A) =ᵐ[haar] ψ := by
  let ψ : C(Cfg, ℝ) :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H 2 specialUnitaryTwoWilsonRankPositive t ht‖⁻¹ •
      p4Q2OU_originalPhysicalTransferContinuous H t ht f
  refine ⟨ψ, ?_⟩
  have hLp :=
    p4Q2OU_originalNormalizedPhysicalTransferContinuous_toLp H t ht f
  rw [hLp]
  exact ψ.coeFn_toLp (p := 2) (𝕜 := ℝ) haar

end ActualPositivePhysicalOneSlab
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OU_originalPhysicalTransferContinuous_toLp
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OU_originalNormalizedPhysicalTransferContinuous_toLp
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OU_originalNormalizedPhysicalTransfer_hasContinuousRepresentative
