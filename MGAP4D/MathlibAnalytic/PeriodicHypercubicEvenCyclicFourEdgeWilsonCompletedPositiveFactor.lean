import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCyclicFourEdgeWilsonPartialFock
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryDensityGramKernel

namespace MGAP4D
namespace MathlibAnalytic

open Filter
open scoped Topology

noncomputable section

private theorem cyclicFourEdgeCompletedPositiveTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance cyclicFourEdgeCompletedPositiveSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

/-- Wilson action carried by the four selected positive-boundary temporal
companions of the canonical primary spatial plaquette, in cyclic pair order
`(2,3)|(0,1)`. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionWilsonAction
    (H : ℕ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin 2) ℂ) : ℝ :=
  (specialUnitaryWilsonPlaquetteEnergy 2
      (periodicHypercubicPlaquetteHolonomy A
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H 2)) +
    specialUnitaryWilsonPlaquetteEnergy 2
      (periodicHypercubicPlaquetteHolonomy A
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H 3))) +
  (specialUnitaryWilsonPlaquetteEnergy 2
      (periodicHypercubicPlaquetteHolonomy A
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H 0)) +
    specialUnitaryWilsonPlaquetteEnergy 2
      (periodicHypercubicPlaquetteHolonomy A
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H 1)))

/-- Algebraic residual positive-boundary temporal action after extracting the
four selected companions.  At this stage it is deliberately defined as a
difference, not asserted to be a literal complement plaquette sum. -/
noncomputable def periodicHypercubicEvenPositiveBoundaryTemporalWilsonResidualAction
    (H : ℕ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin 2) ℂ) : ℝ :=
  periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction H 2 A -
    periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionWilsonAction H A

/-- Boltzmann factor of the algebraic residual action. -/
noncomputable def periodicHypercubicEvenPositiveBoundaryTemporalWilsonResidualWeight
    (H : ℕ)
    (beta : ℝ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin 2) ℂ) : ℝ :=
  Real.exp
    (-beta * periodicHypercubicEvenPositiveBoundaryTemporalWilsonResidualAction H A)

/-- Boltzmann factor of the selected four-companion action. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionWilsonWeight
    (H : ℕ)
    (beta : ℝ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin 2) ℂ) : ℝ :=
  Real.exp
    (-beta *
      periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionWilsonAction H A)

/-- The full positive-boundary temporal weight factors exactly into the
algebraic residual weight and the four selected-companion weight. -/
theorem periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoltzmannWeight_eq_residual_mul_fourCompanion
    (H : ℕ)
    (beta : ℝ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoltzmannWeight H 2 beta A =
      periodicHypercubicEvenPositiveBoundaryTemporalWilsonResidualWeight H beta A *
        periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionWilsonWeight
          H beta A := by
  unfold periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoltzmannWeight
  unfold periodicHypercubicEvenPositiveBoundaryTemporalWilsonResidualWeight
  unfold periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionWilsonWeight
  rw [show
      -beta * periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction H 2 A =
        (-beta * periodicHypercubicEvenPositiveBoundaryTemporalWilsonResidualAction H A) +
          (-beta *
            periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionWilsonAction H A) by
    unfold periodicHypercubicEvenPositiveBoundaryTemporalWilsonResidualAction
    ring]
  exact Real.exp_add _ _

/-- Product of the four literal one-plaquette Wilson Boltzmann factors on an
arbitrary full configuration. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionWilsonProductOnConfiguration
    (H : ℕ)
    (beta : ℝ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin 2) ℂ) : ℝ :=
  (specialUnitaryWilsonBoltzmannCentralFunction 2 beta
      (periodicHypercubicPlaquetteHolonomy A
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H 2)) *
    specialUnitaryWilsonBoltzmannCentralFunction 2 beta
      (periodicHypercubicPlaquetteHolonomy A
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H 3))) *
  (specialUnitaryWilsonBoltzmannCentralFunction 2 beta
      (periodicHypercubicPlaquetteHolonomy A
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H 0)) *
    specialUnitaryWilsonBoltzmannCentralFunction 2 beta
      (periodicHypercubicPlaquetteHolonomy A
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H 1)))

/-- The selected-action exponential is exactly the product of the four literal
one-plaquette Wilson factors. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionWilsonWeight_eq_product
    (H : ℕ)
    (beta : ℝ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionWilsonWeight
        H beta A =
      periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionWilsonProductOnConfiguration
        H beta A := by
  unfold periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionWilsonWeight
  unfold periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionWilsonAction
  unfold periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionWilsonProductOnConfiguration
  unfold specialUnitaryWilsonBoltzmannCentralFunction
  rw [show
      -beta *
          ((specialUnitaryWilsonPlaquetteEnergy 2
                (periodicHypercubicPlaquetteHolonomy A
                  (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H 2)) +
              specialUnitaryWilsonPlaquetteEnergy 2
                (periodicHypercubicPlaquetteHolonomy A
                  (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H 3))) +
            (specialUnitaryWilsonPlaquetteEnergy 2
                (periodicHypercubicPlaquetteHolonomy A
                  (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H 0)) +
              specialUnitaryWilsonPlaquetteEnergy 2
                (periodicHypercubicPlaquetteHolonomy A
                  (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H 1)))) =
        ((-beta * specialUnitaryWilsonPlaquetteEnergy 2
            (periodicHypercubicPlaquetteHolonomy A
              (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H 2))) +
          (-beta * specialUnitaryWilsonPlaquetteEnergy 2
            (periodicHypercubicPlaquetteHolonomy A
              (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H 3)))) +
        ((-beta * specialUnitaryWilsonPlaquetteEnergy 2
            (periodicHypercubicPlaquetteHolonomy A
              (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H 0))) +
          (-beta * specialUnitaryWilsonPlaquetteEnergy 2
            (periodicHypercubicPlaquetteHolonomy A
              (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H 1)))) by
    ring]
  rw [Real.exp_add, Real.exp_add, Real.exp_add]

/-- Positive bulk amplitude completed only by the algebraic residual temporal
weight.  The selected four companions are intentionally excluded from this
factor rather than being assumed trivial. -/
noncomputable def periodicHypercubicEvenResidualCompletedPositiveWilsonBoltzmannAmplitude
    (H : ℕ)
    (beta : ℝ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin 2) ℂ) : ℝ :=
  periodicHypercubicEvenPositiveWilsonBoltzmannAmplitude H 2 beta A *
    periodicHypercubicEvenPositiveBoundaryTemporalWilsonResidualWeight H beta A

/-- Exact completed-positive factorization into residual amplitude and the
four selected actual Wilson plaquette factors. -/
theorem periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude_eq_residual_mul_fourCompanionProduct
    (H : ℕ)
    (beta : ℝ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude H 2 beta A =
      periodicHypercubicEvenResidualCompletedPositiveWilsonBoltzmannAmplitude H beta A *
        periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionWilsonProductOnConfiguration
          H beta A := by
  unfold periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude
  unfold periodicHypercubicEvenResidualCompletedPositiveWilsonBoltzmannAmplitude
  rw [periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoltzmannWeight_eq_residual_mul_fourCompanion]
  rw [periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionWilsonWeight_eq_product]
  ring

/-- Boundary/open-half representative of the residual completed-positive
amplitude, with the unused negative half fixed to identity exactly as in the
existing completed-positive boundary amplitude. -/
noncomputable def periodicHypercubicEvenBoundaryResidualCompletedPositiveWilsonAmplitude
    (H : ℕ)
    (beta : ℝ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ)) : ℝ :=
  periodicHypercubicEvenResidualCompletedPositiveWilsonBoltzmannAmplitude H beta
    ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
      b x (fun _ => 1))

/-- Exact boundary/open-half factorization of the completed-positive amplitude.
The four-companion factor is literally the one already used by the finite Fock
limit theorem. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude_eq_residual_mul_fourCompanionProduct
    (H : ℕ)
    (beta : ℝ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude H 2 beta b x =
      periodicHypercubicEvenBoundaryResidualCompletedPositiveWilsonAmplitude
          H beta b x *
        periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionWilsonBoltzmannProduct
          H beta b x (fun _ => 1) := by
  unfold periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude
  unfold periodicHypercubicEvenBoundaryResidualCompletedPositiveWilsonAmplitude
  rw [periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude_eq_residual_mul_fourCompanionProduct]
  rfl

/-- The boundary Gram prefactor multiplied by the residual completed-positive
amplitude. -/
noncomputable def periodicHypercubicEvenBoundaryCompletedPositiveGramResidualFactor
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ)) : ℝ :=
  Real.sqrt
      (periodicHypercubicEvenBoundaryGramCoefficient
        H 2 cyclicFourEdgeCompletedPositiveTwoRankPositive beta hbeta b) *
    periodicHypercubicEvenBoundaryResidualCompletedPositiveWilsonAmplitude
      H beta b x

/-- Exact factorization of the scalar completed-positive Gram feature into its
residual factor and the four selected actual Wilson factors. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_eq_residual_mul_fourCompanionProduct
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
        H 2 cyclicFourEdgeCompletedPositiveTwoRankPositive beta hbeta b x =
      periodicHypercubicEvenBoundaryCompletedPositiveGramResidualFactor
          H beta hbeta b x *
        periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionWilsonBoltzmannProduct
          H beta b x (fun _ => 1) := by
  unfold periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
  unfold periodicHypercubicEvenBoundaryCompletedPositiveGramResidualFactor
  rw [periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude_eq_residual_mul_fourCompanionProduct]
  ring

/-- Truncated full four-factor Taylor/Fock approximation to the completed
positive Gram feature, with the exact residual Wilson factor held fixed. -/
noncomputable def periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (degree : ℕ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ)) : ℝ :=
  periodicHypercubicEvenBoundaryCompletedPositiveGramResidualFactor
      H beta hbeta b x *
    specialUnitaryTwoCyclicFourEdgeWilsonPartialProductKernel beta degree
      (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b)
      (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfFourEdgeWord H x)

/-- The exact full four-factor finite Taylor/Fock approximation converges
pointwise to the actual completed-positive Gram feature.  The residual factor
is retained exactly throughout the limit. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial_tendsto
    {H : ℕ}
    (hH : 0 < H)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    Tendsto
      (fun degree =>
        periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial
          H beta hbeta degree b x)
      atTop
      (𝓝
        (periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H 2 cyclicFourEdgeCompletedPositiveTwoRankPositive beta hbeta b x)) := by
  have hFour :=
    periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryOpenHalfFourEdgeWilsonPartialKernel_tendsto_actualWilson
      hH beta b x (fun _ => 1)
  have hMul := tendsto_const_nhds.mul hFour
  simpa [periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial,
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_eq_residual_mul_fourCompanionProduct]
    using hMul

end

end MathlibAnalytic
end MGAP4D
