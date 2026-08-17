import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSSymmetricSemigroupCorrelationUniformContinuity
import MGAP4D.MathlibAnalytic.RationalFinToRealUniformContinuousExtension
import Mathlib.Analysis.Normed.Group.Uniform

/-!
# Actual real-insertion OS two-point Euclidean correlation

The symmetric physical OS semigroup already supplies the one-gap autocorrelation
`C_ψ(t) = ⟪ψ, T_t ψ⟫` for nonnegative Euclidean time.  This file packages it as
an actual two-insertion function on `Fin 2 → ℝ` by evaluating at the nonnegative
separation `‖t₁ - t₀‖₊`.

The separation map is Lipschitz, hence the merged uniform continuity of `C_ψ`
gives global uniform continuity in both real insertion times.  The resulting
function is exactly invariant under every common real translation.  Its rational
restriction therefore has the canonical Mathlib dense extension equal to this
actual real OS two-point function.

No identification with the rational path-law connected Schwinger function is
asserted here; that same-root OS reconstruction equality remains a separate
bridge.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- Nonnegative Euclidean separation of two labelled real insertion times. -/
def physicalEuclideanTwoPointSeparation (time : Fin 2 → ℝ) : NNReal :=
  ‖time 1 - time 0‖₊

/-- The two-time separation map is globally Lipschitz. -/
theorem physicalEuclideanTwoPointSeparation_lipschitzWith :
    LipschitzWith 2 physicalEuclideanTwoPointSeparation := by
  have hsub :
      LipschitzWith (2 : NNReal)
        (fun time : Fin 2 → ℝ => time 1 - time 0) := by
    convert
      ((LipschitzWith.eval (α := fun _ : Fin 2 => ℝ) (1 : Fin 2)).sub
        (LipschitzWith.eval (α := fun _ : Fin 2 => ℝ) (0 : Fin 2))) using 1 <;>
      norm_num
  have hnnnorm :
      LipschitzWith (2 : NNReal)
        (fun time : Fin 2 → ℝ => ‖time 1 - time 0‖₊) := by
    simpa using (lipschitzWith_one_nnnorm.comp hsub)
  exact hnnnorm

/-- Common real translation leaves the Euclidean separation unchanged. -/
theorem physicalEuclideanTwoPointSeparation_realCommonShift
    (time : Fin 2 → ℝ) (r : ℝ) :
    physicalEuclideanTwoPointSeparation (MGAP4D.realCommonShift time r) =
      physicalEuclideanTwoPointSeparation time := by
  simp [physicalEuclideanTwoPointSeparation, MGAP4D.realCommonShift]

/-- Actual two-insertion Euclidean OS correlation obtained from the symmetric
physical semigroup autocorrelation. -/
def physicalEuclideanTwoPointCorrelation
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) (time : Fin 2 → ℝ) : ℝ :=
  T.physicalCorrelation psi (physicalEuclideanTwoPointSeparation time)

/-- The actual two-insertion OS correlation is globally uniformly continuous in
both real insertion times. -/
theorem physicalEuclideanTwoPointCorrelation_uniformContinuous
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : P.PhysicalHilbert) :
    UniformContinuous (T.physicalEuclideanTwoPointCorrelation psi) := by
  simpa [physicalEuclideanTwoPointCorrelation] using
    (T.physicalCorrelation_uniformContinuous hSymmetric psi).comp
      physicalEuclideanTwoPointSeparation_lipschitzWith.uniformContinuous

/-- The actual real two-point OS correlation is invariant under every common
real Euclidean-time translation. -/
theorem physicalEuclideanTwoPointCorrelation_realCommonShift
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert)
    (time : Fin 2 → ℝ) (r : ℝ) :
    T.physicalEuclideanTwoPointCorrelation psi
        (MGAP4D.realCommonShift time r) =
      T.physicalEuclideanTwoPointCorrelation psi time := by
  simp [physicalEuclideanTwoPointCorrelation,
    physicalEuclideanTwoPointSeparation_realCommonShift]

/-- Rational restriction of the actual real-insertion OS two-point function. -/
def physicalRationalEuclideanTwoPointCorrelation
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) (time : Fin 2 → ℚ) : ℝ :=
  T.physicalEuclideanTwoPointCorrelation psi (MGAP4D.ratPiCast time)

/-- The rational restriction is uniformly continuous on rational insertion
tuples. -/
theorem physicalRationalEuclideanTwoPointCorrelation_uniformContinuous
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : P.PhysicalHilbert) :
    UniformContinuous (T.physicalRationalEuclideanTwoPointCorrelation psi) := by
  simpa [physicalRationalEuclideanTwoPointCorrelation] using
    (T.physicalEuclideanTwoPointCorrelation_uniformContinuous hSymmetric psi).comp
      (MGAP4D.ratFinCast_isometry 2).uniformContinuous

/-- The canonical Mathlib extension of the rational OS two-point restriction is
exactly the already constructed actual real OS two-point correlation. -/
theorem ratFinUniformlyExtend_physicalRationalEuclideanTwoPointCorrelation_eq
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : P.PhysicalHilbert) :
    MGAP4D.ratFinUniformlyExtend 2
        (T.physicalRationalEuclideanTwoPointCorrelation psi) =
      T.physicalEuclideanTwoPointCorrelation psi := by
  apply MGAP4D.ratFinUniformlyExtend_unique
  · intro time
    rfl
  · exact
      (T.physicalEuclideanTwoPointCorrelation_uniformContinuous
        hSymmetric psi).continuous

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
