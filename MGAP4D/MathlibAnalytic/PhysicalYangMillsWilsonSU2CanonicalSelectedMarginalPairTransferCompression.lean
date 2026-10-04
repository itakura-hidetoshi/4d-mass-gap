import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeProjectiveTransferOperatorBridge
import MGAP4D.MathlibAnalytic.RealLinearIsometryProjectedCompression
import Mathlib.Tactic

/-!
# Canonical selected-marginal realization of the SU(2) physical pair transfer

PR #5085 reduces H1-C3 to one compatible projective finite-marginal operator
system whose selected marginal operators realize the actual normalized physical
pair transfer on the canonical embedded pair-Haar carrier.

The selected-marginal realization itself is not an independent input.

For every scale n, the pair-Haar carrier embeds isometrically into the selected
projective finite marginal. Therefore the actual normalized physical pair
transfer has a canonical bounded ambient realization: project to the closed
range of the pair embedding, pull back through the isometry, apply the actual
pair transfer, and embed again.

This is exactly the existing projected-compression construction.

The remaining H1-C3 input is sharpened to one compatible projective
finite-marginal operator system whose operator at each selected marginal is
exactly this canonical compressed operator.

No H1-D5 compatibility, OS/physical transfer identification, vacuum/top
alignment, or rank-one forcing is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped ENNReal InnerProductSpace InnerProduct Topology

noncomputable section

local instance su2CanonicalSelectedTransferTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance su2CanonicalSelectedTransferCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance su2CanonicalSelectedTransferSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance su2CanonicalSelectedTransferMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance su2CanonicalSelectedTransferBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance su2CanonicalSelectedTransferSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance su2CanonicalSelectedTransferSpatialHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance su2CanonicalSelectedTransferNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

section CanonicalSelectedTransfer

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta)
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout Q F)
    (L : EuclideanYangMillsProjectiveLimitMeasure F)

/-- Canonical ambient selected-marginal realization of the actual normalized
physical pair transfer. -/
noncomputable def physicalYangMillsSU2CanonicalSelectedMarginalPairTransferOperator
    (n : ℕ) :
    Lp ℝ 2 (F.finiteMarginal (R.marginalIndex n)) →L[ℝ]
      Lp ℝ 2 (F.finiteMarginal (R.marginalIndex n)) :=
  realLinearIsometryProjectedCompression
    (physicalYangMillsSU2PairHaarProjectiveFiniteEmbedding Q R n)
    (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
      (halfExtent n) 2 specialUnitaryTwoWilsonRankPositive
      (beta n) (hbeta n))

/-- The canonical selected-marginal operator acts exactly as the actual
normalized physical pair transfer on every embedded pair vector. -/
@[simp]
theorem physicalYangMillsSU2CanonicalSelectedMarginalPairTransferOperator_apply_embedding
    (n : ℕ)
    (x :
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
        (halfExtent n) 2) :
    physicalYangMillsSU2CanonicalSelectedMarginalPairTransferOperator
        Q R n
        (physicalYangMillsSU2PairHaarProjectiveFiniteEmbedding Q R n x) =
      physicalYangMillsSU2PairHaarProjectiveFiniteEmbedding Q R n
        (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
          (halfExtent n) 2 specialUnitaryTwoWilsonRankPositive
          (beta n) (hbeta n) x) := by
  unfold physicalYangMillsSU2CanonicalSelectedMarginalPairTransferOperator
  exact
    realLinearIsometryProjectedCompression_apply_map
      (physicalYangMillsSU2PairHaarProjectiveFiniteEmbedding Q R n)
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
        (halfExtent n) 2 specialUnitaryTwoWilsonRankPositive
        (beta n) (hbeta n))
      x

/-- Projected compression does not increase the actual finite pair-transfer
operator norm. -/
theorem physicalYangMillsSU2CanonicalSelectedMarginalPairTransferOperator_opNorm_le
    (n : ℕ) :
    ‖physicalYangMillsSU2CanonicalSelectedMarginalPairTransferOperator
        Q R n‖ ≤
      ‖periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
        (halfExtent n) 2 specialUnitaryTwoWilsonRankPositive
        (beta n) (hbeta n)‖ := by
  unfold physicalYangMillsSU2CanonicalSelectedMarginalPairTransferOperator
  exact
    realLinearIsometryProjectedCompression_opNorm_le
      (physicalYangMillsSU2PairHaarProjectiveFiniteEmbedding Q R n)
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
        (halfExtent n) 2 specialUnitaryTwoWilsonRankPositive
        (beta n) (hbeta n))

/-- Sharpened H1-C3 input: one globally compatible finite-marginal projective
operator system extending the canonically compressed selected operators. -/
structure PhysicalYangMillsSU2CanonicalSelectedMarginalPairTransferExtensionInput where
  operatorSystem :
    EuclideanYangMillsProjectiveLimitL2OperatorSystem F L
  selectedLocalOperator_eq_canonical :
    ∀ n : ℕ,
      operatorSystem.localOperator (R.marginalIndex n) =
        physicalYangMillsSU2CanonicalSelectedMarginalPairTransferOperator
          Q R n

namespace PhysicalYangMillsSU2CanonicalSelectedMarginalPairTransferExtensionInput

variable
    (C :
      PhysicalYangMillsSU2CanonicalSelectedMarginalPairTransferExtensionInput
        Q R L)

/-- The sharpened canonical extension input theorem-generates the #5085
pointwise operator bridge. -/
noncomputable def toProjectivePairTransferOperatorBridgeInput :
    PhysicalYangMillsSU2ProjectivePairTransferOperatorBridgeInput
      Q R L where
  operatorSystem := C.operatorSystem
  selectedLocalOperator_intertwines_pairTransfer := by
    intro n x
    rw [C.selectedLocalOperator_eq_canonical n]
    exact
      physicalYangMillsSU2CanonicalSelectedMarginalPairTransferOperator_apply_embedding
        Q R n x

/-- One compatible global extension of the canonical selected operators yields
same-subsequence strong limits at every natural transfer time. -/
theorem
    physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_sameSubsequence_evolved_strong_limits_of_canonicalExtension
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (G :
      PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
        S D halfExtent beta hbeta Q F R L hInvariant) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∃ y : Lp ℝ 2 L.continuumMeasure,
        ‖y‖ = 1 ∧
        ∀ m : ℕ,
          Tendsto
            (fun j =>
              physicalYangMillsVacuumNormalizedSU2ThreeModeEvolvedProjectiveContinuumImage
                Q R L hInvariant (phi j) m)
            atTop
            (𝓝
              ((PhysicalYangMillsSU2ProjectivePairTransferOperatorBridgeInput.continuumTransfer Q R L
                  (toProjectivePairTransferOperatorBridgeInput Q R L C) ^ m) y)) := by
  exact
    PhysicalYangMillsSU2ProjectivePairTransferOperatorBridgeInput.physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_sameSubsequence_evolved_strong_limits
      Q R L
      (toProjectivePairTransferOperatorBridgeInput Q R L C)
      hInvariant G

/-- The sharpened canonical extension input also yields the complete
same-subsequence discrete-time q0 package from #5085. -/
theorem
    physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_continuumDiscreteTime_q0_of_canonicalExtension
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (G :
      PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
        S D halfExtent beta hbeta Q F R L hInvariant)
    (s : ℝ) (hs : 8 < s)
    (hcut :
      ∀ n : ℕ,
        beta n ≤
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
            s hs) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∃ y : Lp ℝ 2 L.continuumMeasure,
        ‖y‖ = 1 ∧
        ∀ m : ℕ,
          Tendsto
              (fun j =>
                physicalYangMillsVacuumNormalizedSU2ThreeModeEvolvedProjectiveContinuumImage
                  Q R L hInvariant (phi j) m)
              atTop
              (𝓝
                ((PhysicalYangMillsSU2ProjectivePairTransferOperatorBridgeInput.continuumTransfer Q R L
                    (toProjectivePairTransferOperatorBridgeInput Q R L C) ^ m) y)) ∧
            ‖(PhysicalYangMillsSU2ProjectivePairTransferOperatorBridgeInput.continuumTransfer Q R L
                (toProjectivePairTransferOperatorBridgeInput Q R L C) ^ m) y‖ ≤
              GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ m := by
  exact
    PhysicalYangMillsSU2ProjectivePairTransferOperatorBridgeInput.physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_continuumDiscreteTime_q0
      Q R L
      (toProjectivePairTransferOperatorBridgeInput Q R L C)
      hInvariant G s hs hcut

end PhysicalYangMillsSU2CanonicalSelectedMarginalPairTransferExtensionInput

end CanonicalSelectedTransfer

end

end MathlibAnalytic
end MGAP4D
