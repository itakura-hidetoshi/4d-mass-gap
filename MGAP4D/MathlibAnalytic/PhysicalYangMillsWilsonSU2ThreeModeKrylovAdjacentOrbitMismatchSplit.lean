import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentOrbitMismatch
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentTransferMismatchSplit
import MGAP4D.MathlibAnalytic.ContinuousLinearMapContractionPowerPerturbation
import Mathlib.Tactic

/-!
# Split vector-wise Krylov-orbit mismatch into geometry and coupling

PR #5105 splits the whole-space adjacent common-transfer mismatch into a
cross-volume geometry residual and a same-fine-volume coupling residual.

PR #5106 shows that the strong-limit argument does not need the whole-space
operator norm: it only needs the adjacent transfer mismatch on each fixed
fine-side Krylov-orbit vector.

Combining those two ideas gives the sharper model-facing estimate

  orbitMismatch(n,r,k)
    <= orbitGeometryResidual(n,r,k) + couplingResidual(n).

Only the geometry term remains vector-wise.  The coupling term is a same-volume
operator-norm difference of normalized physical pair transfers and is therefore
amenable to Wilson-coupling regularity estimates without any cross-volume
operator compatibility.

If every fixed orbit-geometry residual is summable in n and the single coupling
residual is summable in n, then the #5106 orbit-summability input follows and
all fixed-natural-time strong limits are theorem-generated.  This complements
merged #5107, which packages geometric decay of the unsplit orbit mismatch.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped ENNReal InnerProductSpace InnerProduct Topology

noncomputable section

local instance su2AdjacentOrbitSplitTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance su2AdjacentOrbitSplitCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance su2AdjacentOrbitSplitSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance su2AdjacentOrbitSplitMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance su2AdjacentOrbitSplitBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance su2AdjacentOrbitSplitSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance su2AdjacentOrbitSplitSpatialHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance

local instance su2AdjacentOrbitSplitNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

section AdjacentOrbitGeometryCouplingSplit

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

/-- The actual fine-side r-th Krylov-orbit vector in the adjacent common
marginal. -/
noncomputable def physicalYangMillsSU2AdjacentCommonRightOrbitVector
    (n r : ℕ) (k : Fin 3) :
    Lp ℝ 2
        (F.finiteMarginal
          (physicalYangMillsSU2ThreeModeAdjacentCommonMarginalIndex
            (Q := Q) R n)) :=
  (physicalYangMillsSU2AdjacentCommonRightTransfer Q R n ^ r)
    (physicalYangMillsSU2AdjacentCommonRightInitialKrylovMode Q R n k)

/-- Every actual fine-side orbit vector remains in the unit ball. -/
theorem physicalYangMillsSU2AdjacentCommonRightOrbitVector_norm_le_one
    (n r : ℕ) (k : Fin 3) :
    ‖physicalYangMillsSU2AdjacentCommonRightOrbitVector Q R n r k‖ ≤ 1 := by
  have hpow :
      ‖physicalYangMillsSU2AdjacentCommonRightTransfer Q R n ^ r‖ ≤ 1 :=
    continuousLinearMap_pow_norm_le_one_of_norm_le_one
      (physicalYangMillsSU2AdjacentCommonRightTransfer Q R n)
      (physicalYangMillsSU2AdjacentCommonRightTransfer_opNorm_le_one Q R n)
      r
  have hv :
      ‖physicalYangMillsSU2AdjacentCommonRightInitialKrylovMode Q R n k‖ ≤ 1 := by
    exact le_of_eq
      (physicalYangMillsSU2AdjacentCommonRightInitialKrylovMode_norm Q R n k)
  unfold physicalYangMillsSU2AdjacentCommonRightOrbitVector
  calc
    ‖(physicalYangMillsSU2AdjacentCommonRightTransfer Q R n ^ r)
        (physicalYangMillsSU2AdjacentCommonRightInitialKrylovMode Q R n k)‖ ≤
      ‖physicalYangMillsSU2AdjacentCommonRightTransfer Q R n ^ r‖ *
        ‖physicalYangMillsSU2AdjacentCommonRightInitialKrylovMode Q R n k‖ :=
      (physicalYangMillsSU2AdjacentCommonRightTransfer Q R n ^ r).le_opNorm _
    _ ≤ 1 * 1 := by
      exact mul_le_mul hpow hv
        (norm_nonneg
          (physicalYangMillsSU2AdjacentCommonRightInitialKrylovMode Q R n k))
        zero_le_one
    _ = 1 := by norm_num

/-- Cross-volume geometry residual evaluated only on the actual fine-side
Krylov-orbit vector. -/
noncomputable def physicalYangMillsSU2AdjacentCommonTransferOrbitGeometryResidual
    (n r : ℕ) (k : Fin 3) : ℝ :=
  ‖(physicalYangMillsSU2AdjacentCommonLeftTransfer Q R n -
      physicalYangMillsSU2AdjacentCommonRightTransferAtCoupling
        Q R n (beta n) (hbeta n))
      (physicalYangMillsSU2AdjacentCommonRightOrbitVector Q R n r k)‖

theorem physicalYangMillsSU2AdjacentCommonTransferOrbitGeometryResidual_nonneg
    (n r : ℕ) (k : Fin 3) :
    0 ≤
      physicalYangMillsSU2AdjacentCommonTransferOrbitGeometryResidual
        Q R n r k :=
  norm_nonneg _

/-- Same-fine-volume normalized physical pair-transfer coupling residual. -/
noncomputable def physicalYangMillsSU2AdjacentCommonTransferCouplingResidual
    (n : ℕ) : ℝ :=
  ‖periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
      (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
      (beta n) (hbeta n) -
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
      (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
      (beta (n + 1)) (hbeta (n + 1))‖

theorem physicalYangMillsSU2AdjacentCommonTransferCouplingResidual_nonneg
    (n : ℕ) :
    0 ≤ physicalYangMillsSU2AdjacentCommonTransferCouplingResidual Q R n :=
  norm_nonneg _

/-- The coupling part of the adjacent compression mismatch, when applied to any
actual fine-side Krylov-orbit vector, is bounded by the same-volume normalized
physical pair-transfer coupling residual. -/
theorem physicalYangMillsSU2AdjacentCommonRightCouplingOrbitMismatch_le
    (n r : ℕ) (k : Fin 3) :
    ‖(physicalYangMillsSU2AdjacentCommonRightTransferAtCoupling
          Q R n (beta n) (hbeta n) -
        physicalYangMillsSU2AdjacentCommonRightTransfer Q R n)
        (physicalYangMillsSU2AdjacentCommonRightOrbitVector Q R n r k)‖ ≤
      physicalYangMillsSU2AdjacentCommonTransferCouplingResidual Q R n := by
  have hz :
      ‖physicalYangMillsSU2AdjacentCommonRightOrbitVector Q R n r k‖ ≤ 1 :=
    physicalYangMillsSU2AdjacentCommonRightOrbitVector_norm_le_one
      Q R n r k
  have hop :
      ‖physicalYangMillsSU2AdjacentCommonRightTransferAtCoupling
            Q R n (beta n) (hbeta n) -
          physicalYangMillsSU2AdjacentCommonRightTransfer Q R n‖ ≤
        physicalYangMillsSU2AdjacentCommonTransferCouplingResidual Q R n := by
    rw [← physicalYangMillsSU2AdjacentCommonRightTransferAtCoupling_beta_succ
      Q R n]
    exact
      physicalYangMillsSU2AdjacentCommonRightTransferAtCoupling_norm_sub_le
        Q R n (beta n) (beta (n + 1)) (hbeta n) (hbeta (n + 1))
  calc
    ‖(physicalYangMillsSU2AdjacentCommonRightTransferAtCoupling
          Q R n (beta n) (hbeta n) -
        physicalYangMillsSU2AdjacentCommonRightTransfer Q R n)
        (physicalYangMillsSU2AdjacentCommonRightOrbitVector Q R n r k)‖ ≤
      ‖physicalYangMillsSU2AdjacentCommonRightTransferAtCoupling
          Q R n (beta n) (hbeta n) -
        physicalYangMillsSU2AdjacentCommonRightTransfer Q R n‖ *
      ‖physicalYangMillsSU2AdjacentCommonRightOrbitVector Q R n r k‖ :=
      (physicalYangMillsSU2AdjacentCommonRightTransferAtCoupling
          Q R n (beta n) (hbeta n) -
        physicalYangMillsSU2AdjacentCommonRightTransfer Q R n).le_opNorm _
    _ ≤
      physicalYangMillsSU2AdjacentCommonTransferCouplingResidual Q R n * 1 := by
      exact mul_le_mul hop hz
        (norm_nonneg
          (physicalYangMillsSU2AdjacentCommonRightOrbitVector Q R n r k))
        (physicalYangMillsSU2AdjacentCommonTransferCouplingResidual_nonneg
          Q R n)
    _ =
      physicalYangMillsSU2AdjacentCommonTransferCouplingResidual Q R n := by
      rw [mul_one]

/-- Sharpened model-facing split on the finite Krylov orbit: full adjacent orbit
mismatch is bounded by a vector-wise geometry residual plus a same-volume
coupling residual. -/
theorem physicalYangMillsSU2AdjacentCommonTransferRightOrbitMismatch_le_geometry_add_coupling
    (n r : ℕ) (k : Fin 3) :
    physicalYangMillsSU2AdjacentCommonTransferRightOrbitMismatch Q R n r k ≤
      physicalYangMillsSU2AdjacentCommonTransferOrbitGeometryResidual
          Q R n r k +
        physicalYangMillsSU2AdjacentCommonTransferCouplingResidual Q R n := by
  let z := physicalYangMillsSU2AdjacentCommonRightOrbitVector Q R n r k
  have hsplit :
      (physicalYangMillsSU2AdjacentCommonLeftTransfer Q R n -
          physicalYangMillsSU2AdjacentCommonRightTransfer Q R n) z =
        (physicalYangMillsSU2AdjacentCommonLeftTransfer Q R n -
            physicalYangMillsSU2AdjacentCommonRightTransferAtCoupling
              Q R n (beta n) (hbeta n)) z +
          (physicalYangMillsSU2AdjacentCommonRightTransferAtCoupling
              Q R n (beta n) (hbeta n) -
            physicalYangMillsSU2AdjacentCommonRightTransfer Q R n) z := by
    simp only [ContinuousLinearMap.sub_apply]
    abel
  unfold physicalYangMillsSU2AdjacentCommonTransferRightOrbitMismatch
  change
    ‖(physicalYangMillsSU2AdjacentCommonLeftTransfer Q R n -
        physicalYangMillsSU2AdjacentCommonRightTransfer Q R n) z‖ ≤ _
  rw [hsplit]
  calc
    ‖(physicalYangMillsSU2AdjacentCommonLeftTransfer Q R n -
          physicalYangMillsSU2AdjacentCommonRightTransferAtCoupling
            Q R n (beta n) (hbeta n)) z +
        (physicalYangMillsSU2AdjacentCommonRightTransferAtCoupling
            Q R n (beta n) (hbeta n) -
          physicalYangMillsSU2AdjacentCommonRightTransfer Q R n) z‖ ≤
      ‖(physicalYangMillsSU2AdjacentCommonLeftTransfer Q R n -
          physicalYangMillsSU2AdjacentCommonRightTransferAtCoupling
            Q R n (beta n) (hbeta n)) z‖ +
        ‖(physicalYangMillsSU2AdjacentCommonRightTransferAtCoupling
            Q R n (beta n) (hbeta n) -
          physicalYangMillsSU2AdjacentCommonRightTransfer Q R n) z‖ :=
      norm_add_le _ _
    _ ≤
      physicalYangMillsSU2AdjacentCommonTransferOrbitGeometryResidual
          Q R n r k +
        physicalYangMillsSU2AdjacentCommonTransferCouplingResidual Q R n := by
      change
        ‖(physicalYangMillsSU2AdjacentCommonLeftTransfer Q R n -
            physicalYangMillsSU2AdjacentCommonRightTransferAtCoupling
              Q R n (beta n) (hbeta n)) z‖ +
          ‖(physicalYangMillsSU2AdjacentCommonRightTransferAtCoupling
              Q R n (beta n) (hbeta n) -
            physicalYangMillsSU2AdjacentCommonRightTransfer Q R n) z‖ ≤ _
      unfold physicalYangMillsSU2AdjacentCommonTransferOrbitGeometryResidual
      change
        ‖(physicalYangMillsSU2AdjacentCommonLeftTransfer Q R n -
            physicalYangMillsSU2AdjacentCommonRightTransferAtCoupling
              Q R n (beta n) (hbeta n)) z‖ +
          ‖(physicalYangMillsSU2AdjacentCommonRightTransferAtCoupling
              Q R n (beta n) (hbeta n) -
            physicalYangMillsSU2AdjacentCommonRightTransfer Q R n) z‖ ≤
        ‖(physicalYangMillsSU2AdjacentCommonLeftTransfer Q R n -
            physicalYangMillsSU2AdjacentCommonRightTransferAtCoupling
              Q R n (beta n) (hbeta n)) z‖ +
          physicalYangMillsSU2AdjacentCommonTransferCouplingResidual Q R n
      exact
        add_le_add_right
          (physicalYangMillsSU2AdjacentCommonRightCouplingOrbitMismatch_le
            Q R n r k)
          ‖(physicalYangMillsSU2AdjacentCommonLeftTransfer Q R n -
            physicalYangMillsSU2AdjacentCommonRightTransferAtCoupling
              Q R n (beta n) (hbeta n)) z‖

/-- Summability of the vector-wise geometry residuals together with summability
of the single same-volume coupling residual is sufficient for the #5106
orbit-summability input. -/
structure PhysicalYangMillsSU2AdjacentOrbitGeometryCouplingSummableInput where
  orbitGeometry_summable :
    ∀ (r : ℕ) (k : Fin 3),
      Summable
        (fun n =>
          physicalYangMillsSU2AdjacentCommonTransferOrbitGeometryResidual
            Q R n r k)
  coupling_summable :
    Summable
      (fun n =>
        physicalYangMillsSU2AdjacentCommonTransferCouplingResidual Q R n)

namespace PhysicalYangMillsSU2AdjacentOrbitGeometryCouplingSummableInput

variable
    (G :
      PhysicalYangMillsSU2AdjacentOrbitGeometryCouplingSummableInput
        (Q := Q) (R := R))

include G

/-- Geometry-plus-coupling summability implies every fixed orbit mismatch is
summable in the refinement scale. -/
theorem orbitMismatch_summable
    (r : ℕ) (k : Fin 3) :
    Summable
      (fun n =>
        physicalYangMillsSU2AdjacentCommonTransferRightOrbitMismatch
          Q R n r k) := by
  have hmajorant :
      Summable
        (fun n =>
          physicalYangMillsSU2AdjacentCommonTransferOrbitGeometryResidual
              Q R n r k +
            physicalYangMillsSU2AdjacentCommonTransferCouplingResidual Q R n) :=
    (G.orbitGeometry_summable r k).add G.coupling_summable
  refine Summable.of_nonneg_of_le
    (fun n => ?_)
    (fun n =>
      physicalYangMillsSU2AdjacentCommonTransferRightOrbitMismatch_le_geometry_add_coupling
        Q R n r k)
    hmajorant
  unfold physicalYangMillsSU2AdjacentCommonTransferRightOrbitMismatch
  exact norm_nonneg _

/-- Produce the exact #5106 orbit-summability package. -/
noncomputable def toOrbitMismatchSummableInput :
    PhysicalYangMillsSU2AdjacentCommonTransferOrbitMismatchSummableInput
      (Q := Q) (R := R) where
  orbitMismatch_summable := orbitMismatch_summable Q R G

/-- Separate summability of orbit geometry and same-volume coupling therefore
gives all fixed-natural-time strong limits. -/
theorem
    physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_evolved_strong_limits
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C :
      PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
        S D halfExtent beta hbeta Q F R L hInvariant) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∃ cInf : EuclideanSpace ℝ (Fin 3),
        ‖cInf‖ = 1 ∧
        ∀ m : ℕ,
          Tendsto
            (fun j =>
              physicalYangMillsVacuumNormalizedSU2ThreeModeEvolvedProjectiveContinuumImage
                Q R L hInvariant (phi j) m)
            atTop
            (𝓝
              (PhysicalYangMillsSU2ThreeModeEvolvedBasisCoherenceInput.continuumSynthesis
                Q R L
                (PhysicalYangMillsSU2ThreeModeFiniteAdjacentKrylovSummableInput.toEvolvedBasisCoherenceInput
                  Q R L
                  (PhysicalYangMillsSU2AdjacentCommonTransferOrbitMismatchSummableInput.toFiniteAdjacentKrylovSummableInput
                    Q R L (toOrbitMismatchSummableInput Q R G) hInvariant C))
                m cInf)) := by
  exact
    PhysicalYangMillsSU2AdjacentCommonTransferOrbitMismatchSummableInput.physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_evolved_strong_limits
      Q R L (toOrbitMismatchSummableInput Q R G) hInvariant C

/-- The same separated summability input retains the uniform q0^m continuum
decay. -/
theorem
    physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_evolved_strong_limits_q0
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C :
      PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
        S D halfExtent beta hbeta Q F R L hInvariant)
    (s : ℝ) (hs : 8 < s)
    (hcut :
      ∀ n : ℕ,
        beta n ≤
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
            s hs) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∃ cInf : EuclideanSpace ℝ (Fin 3),
        ‖cInf‖ = 1 ∧
        ∀ m : ℕ,
          Tendsto
              (fun j =>
                physicalYangMillsVacuumNormalizedSU2ThreeModeEvolvedProjectiveContinuumImage
                  Q R L hInvariant (phi j) m)
              atTop
              (𝓝
                (PhysicalYangMillsSU2ThreeModeEvolvedBasisCoherenceInput.continuumSynthesis
                  Q R L
                  (PhysicalYangMillsSU2ThreeModeFiniteAdjacentKrylovSummableInput.toEvolvedBasisCoherenceInput
                    Q R L
                    (PhysicalYangMillsSU2AdjacentCommonTransferOrbitMismatchSummableInput.toFiniteAdjacentKrylovSummableInput
                      Q R L (toOrbitMismatchSummableInput Q R G) hInvariant C))
                  m cInf)) ∧
            ‖PhysicalYangMillsSU2ThreeModeEvolvedBasisCoherenceInput.continuumSynthesis
                Q R L
                (PhysicalYangMillsSU2ThreeModeFiniteAdjacentKrylovSummableInput.toEvolvedBasisCoherenceInput
                  Q R L
                  (PhysicalYangMillsSU2AdjacentCommonTransferOrbitMismatchSummableInput.toFiniteAdjacentKrylovSummableInput
                    Q R L (toOrbitMismatchSummableInput Q R G) hInvariant C))
                m cInf‖ ≤
              GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ m := by
  exact
    PhysicalYangMillsSU2AdjacentCommonTransferOrbitMismatchSummableInput.physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_evolved_strong_limits_q0
      Q R L (toOrbitMismatchSummableInput Q R G) hInvariant C s hs hcut

end PhysicalYangMillsSU2AdjacentOrbitGeometryCouplingSummableInput

end AdjacentOrbitGeometryCouplingSplit

end

end MathlibAnalytic
end MGAP4D
