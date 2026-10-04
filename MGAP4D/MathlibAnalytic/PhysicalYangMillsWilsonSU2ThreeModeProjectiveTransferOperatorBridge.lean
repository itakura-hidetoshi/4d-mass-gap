import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeEvolvedProjectiveQ0Limit
import MGAP4D.MathlibAnalytic.EuclideanYangMillsProjectiveLimitL2CompatibleOperatorExtension
import Mathlib.Tactic

/-!
# Compatible projective operator bridge for the SU(2) three-mode excitation

PR #5083 constructs a norm-one nonzero projective strong limit for the exact
finite SU(2) three-mode physical non-top excitation.  PR #5084 shows that any
strong limit of its genuinely evolved finite images automatically inherits the
uniform q0^m estimate.

The remaining H1-C3 issue is therefore operator coherence, not a new decay
estimate.

This file isolates the exact missing operator datum and then uses the already
proved projective-limit finite-marginal operator-extension theorem.

The input is one uniformly bounded compatible operator system on all finite
projective marginals whose selected marginal operator acts on the canonical
embedded pair-Haar carrier exactly as the actual normalized physical pair
transfer.

From that input, Mathlib/projective infrastructure theorem-generates one
bounded continuum operator T.  It satisfies exact finite-to-continuum
intertwining

  T (Embed_n x) = Embed_n (S_n x)

and hence, for every natural m,

  T^m (Embed_n x) = Embed_n (S_n^m x).

Applying continuity of T^m to the #5083 initial strong limit gives strong
limits of all evolved finite excitations along the *same* subsequence, with
limit T^m y.  PR #5084 then yields

  ||T^m y|| <= q0^m,

while ||y|| = 1.

Thus H1-C3 is reduced to a concrete selected-marginal operator realization
inside an otherwise already-closed compatible projective operator system.

This is not H1-D5: no OS-boundary transfer is identified with the physical
pair transfer, no vacuum/top alignment appears, and no rank-one condition is
introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped ENNReal InnerProductSpace InnerProduct Topology

noncomputable section

local instance su2ProjectiveTransferBridgeTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance su2ProjectiveTransferBridgeCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance su2ProjectiveTransferBridgeSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance su2ProjectiveTransferBridgeMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance su2ProjectiveTransferBridgeBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance su2ProjectiveTransferBridgeSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance su2ProjectiveTransferBridgeSpatialHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance su2ProjectiveTransferBridgeNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

section Bridge

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

/-- Canonical isometric embedding of the actual ordered pair-Haar carrier into
the selected interacting projective finite marginal. -/
noncomputable def physicalYangMillsSU2PairHaarProjectiveFiniteEmbedding
    (n : ℕ) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
        (halfExtent n) 2 →ₗᵢ[ℝ]
      Lp ℝ 2 (F.finiteMarginal (R.marginalIndex n)) :=
  (R.boundaryHaarProjectiveL2Isometry n).comp
    (periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry
      (halfExtent n) 2)

@[simp]
theorem physicalYangMillsSU2PairHaarProjectiveFiniteEmbedding_norm
    (n : ℕ)
    (x :
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
        (halfExtent n) 2) :
    ‖physicalYangMillsSU2PairHaarProjectiveFiniteEmbedding Q R n x‖ = ‖x‖ :=
  (physicalYangMillsSU2PairHaarProjectiveFiniteEmbedding Q R n).norm_map x

/-- The #5083 common-continuum embedding factors exactly through the selected
finite projective marginal embedding. -/
theorem physicalYangMillsSU2PairHaarProjectiveContinuumEmbedding_eq_finitePullback
    (n : ℕ)
    (x :
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
        (halfExtent n) 2) :
    physicalYangMillsSU2PairHaarProjectiveContinuumEmbedding Q R L n x =
      L.finiteMarginalL2Pullback (R.marginalIndex n)
        (physicalYangMillsSU2PairHaarProjectiveFiniteEmbedding Q R n x) := by
  rfl

/-- The genuinely missing H1-C3 operator realization datum.

The projective operator system already carries exact transition compatibility
and a uniform operator bound on *all* finite marginals.  The only additional
model-facing statement here is that its operator on each selected Wilson
marginal realizes the actual normalized physical pair transfer on the
canonically embedded pair-Haar carrier. -/
structure PhysicalYangMillsSU2ProjectivePairTransferOperatorBridgeInput where
  operatorSystem :
    EuclideanYangMillsProjectiveLimitL2OperatorSystem F L
  selectedLocalOperator_intertwines_pairTransfer :
    ∀ (n : ℕ)
      (x :
        PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
          (halfExtent n) 2),
      operatorSystem.localOperator (R.marginalIndex n)
          (physicalYangMillsSU2PairHaarProjectiveFiniteEmbedding Q R n x) =
        physicalYangMillsSU2PairHaarProjectiveFiniteEmbedding Q R n
          (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
            (halfExtent n) 2 specialUnitaryTwoWilsonRankPositive
            (beta n) (hbeta n) x)

namespace PhysicalYangMillsSU2ProjectivePairTransferOperatorBridgeInput

variable
    (I : PhysicalYangMillsSU2ProjectivePairTransferOperatorBridgeInput
      Q R L)

/-- The bounded continuum projective-limit operator theorem-generated by the
compatible finite-marginal system. -/
noncomputable def continuumTransfer :
    Lp ℝ 2 L.continuumMeasure →L[ℝ]
      Lp ℝ 2 L.continuumMeasure :=
  L.finiteMarginalL2ContinuumOperator I.operatorSystem

/-- The continuum operator inherits the common full finite-marginal norm
bound from the compatible operator system. -/
theorem continuumTransfer_norm_le
    (x : Lp ℝ 2 L.continuumMeasure) :
    ‖I.continuumTransfer x‖ ≤ I.operatorSystem.bound * ‖x‖ := by
  exact
    L.finiteMarginalL2ContinuumOperator_norm_le
      I.operatorSystem x

/-- The continuum operator norm is bounded by the same projective-system
constant. -/
theorem continuumTransfer_opNorm_le :
    ‖I.continuumTransfer‖ ≤ I.operatorSystem.bound := by
  exact
    L.finiteMarginalL2ContinuumOperator_opNorm_le
      I.operatorSystem

/-- Exact one-step actual-pair to continuum intertwining. -/
theorem continuumTransfer_intertwines_pairTransfer
    (n : ℕ)
    (x :
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
        (halfExtent n) 2) :
    I.continuumTransfer
        (physicalYangMillsSU2PairHaarProjectiveContinuumEmbedding
          Q R L n x) =
      physicalYangMillsSU2PairHaarProjectiveContinuumEmbedding
        Q R L n
        (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
          (halfExtent n) 2 specialUnitaryTwoWilsonRankPositive
          (beta n) (hbeta n) x) := by
  rw [
    physicalYangMillsSU2PairHaarProjectiveContinuumEmbedding_eq_finitePullback
      Q R L n x,
    physicalYangMillsSU2PairHaarProjectiveContinuumEmbedding_eq_finitePullback
      Q R L n
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
        (halfExtent n) 2 specialUnitaryTwoWilsonRankPositive
        (beta n) (hbeta n) x)]
  unfold continuumTransfer
  rw [
    L.finiteMarginalL2ContinuumOperator_intertwines
      I.operatorSystem (R.marginalIndex n)
      (physicalYangMillsSU2PairHaarProjectiveFiniteEmbedding Q R n x),
    I.selectedLocalOperator_intertwines_pairTransfer n x]

/-- Exact intertwining persists for every natural power. -/
theorem continuumTransfer_pow_intertwines_pairTransfer
    (n m : ℕ)
    (x :
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
        (halfExtent n) 2) :
    (I.continuumTransfer ^ m)
        (physicalYangMillsSU2PairHaarProjectiveContinuumEmbedding
          Q R L n x) =
      physicalYangMillsSU2PairHaarProjectiveContinuumEmbedding
        Q R L n
        ((periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
          (halfExtent n) 2 specialUnitaryTwoWilsonRankPositive
          (beta n) (hbeta n) ^ m) x) := by
  let T := I.continuumTransfer
  let Sn :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
      (halfExtent n) 2 specialUnitaryTwoWilsonRankPositive
      (beta n) (hbeta n)
  let J :=
    physicalYangMillsSU2PairHaarProjectiveContinuumEmbedding
      Q R L n
  change (T ^ m) (J x) = J ((Sn ^ m) x)
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
      change (T ^ m) (T (J x)) = J ((Sn ^ m) (Sn x))
      have hstep : T (J x) = J (Sn x) := by
        simpa [T, Sn, J] using
          I.continuumTransfer_intertwines_pairTransfer n x
      rw [hstep]
      exact ih (Sn x)

/-- The #5084 genuinely evolved embedded excitation is exactly the m-th power
of the single continuum operator applied to the corresponding finite initial
embedded excitation. -/
theorem
    physicalYangMillsVacuumNormalizedSU2ThreeModeEvolvedProjectiveContinuumImage_eq_continuumTransfer_pow
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n m : ℕ) :
    physicalYangMillsVacuumNormalizedSU2ThreeModeEvolvedProjectiveContinuumImage
        Q R L hInvariant n m =
      (I.continuumTransfer ^ m)
        (physicalYangMillsSU2PairHaarProjectiveContinuumEmbedding
          Q R L n
          (physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice
            Q hInvariant n)) := by
  unfold
    physicalYangMillsVacuumNormalizedSU2ThreeModeEvolvedProjectiveContinuumImage
  exact
    (I.continuumTransfer_pow_intertwines_pairTransfer
      n m
      (physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice
        Q hInvariant n)).symm

/-- Once the compatible operator bridge exists, the #5083 initial strong-limit
subsequence automatically gives strong limits of *all* natural-time evolved
images along that same subsequence, with limit T^m y. -/
theorem
    physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_sameSubsequence_evolved_strong_limits
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C :
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
            (𝓝 ((I.continuumTransfer ^ m) y)) := by
  obtain ⟨phi, hphi, cInf, hcInf, hInitial, hyNorm⟩ :=
    physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_projective_strong_limit
      Q R L hInvariant C
  let y :=
    physicalYangMillsSU2ThreeModeContinuumSynthesis
      Q R L hInvariant C cInf
  refine ⟨phi, hphi, y, by simpa [y] using hyNorm, ?_⟩
  intro m
  have hPow :
      Tendsto
        (fun j =>
          (I.continuumTransfer ^ m)
            (physicalYangMillsSU2PairHaarProjectiveContinuumEmbedding
              Q R L (phi j)
              (physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice
                Q hInvariant (phi j))))
        atTop
        (𝓝 ((I.continuumTransfer ^ m) y)) := by
    have hMap :=
      (((I.continuumTransfer ^ m).continuous.tendsto y).comp hInitial)
    simpa [y] using hMap
  apply hPow.congr'
  exact Filter.Eventually.of_forall fun j =>
    (I.physicalYangMillsVacuumNormalizedSU2ThreeModeEvolvedProjectiveContinuumImage_eq_continuumTransfer_pow
      hInvariant (phi j) m).symm

/-- H1-C3 quantitative package on the theorem-generated nonzero continuum
initial excitation.

The same subsequence works for every fixed natural time, the limits are the
powers of one bounded continuum operator, and every such limit inherits the
already-proved q0^m estimate. -/
theorem
    physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_continuumDiscreteTime_q0
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
      ∃ y : Lp ℝ 2 L.continuumMeasure,
        ‖y‖ = 1 ∧
        ∀ m : ℕ,
          Tendsto
              (fun j =>
                physicalYangMillsVacuumNormalizedSU2ThreeModeEvolvedProjectiveContinuumImage
                  Q R L hInvariant (phi j) m)
              atTop
              (𝓝 ((I.continuumTransfer ^ m) y)) ∧
            ‖(I.continuumTransfer ^ m) y‖ ≤
              GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ m := by
  obtain ⟨phi, hphi, y, hyNorm, hStrong⟩ :=
    I.physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_sameSubsequence_evolved_strong_limits
      hInvariant C
  refine ⟨phi, hphi, y, hyNorm, ?_⟩
  intro m
  refine ⟨hStrong m, ?_⟩
  exact
    physicalYangMillsVacuumNormalizedSU2ThreeModeEvolvedProjectiveStrongLimit_norm_le_uniform_q0
      Q R L hInvariant s hs hcut phi m
      ((I.continuumTransfer ^ m) y)
      (hStrong m)

/-- The continuum natural-time limits are automatically semigroup-compatible:
the m+k limit is obtained by applying T^m to the k limit. -/
theorem continuumTransfer_pow_add_apply
    (m k : ℕ)
    (y : Lp ℝ 2 L.continuumMeasure) :
    (I.continuumTransfer ^ (m + k)) y =
      (I.continuumTransfer ^ m) ((I.continuumTransfer ^ k) y) := by
  rw [pow_add]
  rfl

end PhysicalYangMillsSU2ProjectivePairTransferOperatorBridgeInput

end Bridge

end

end MathlibAnalytic
end MGAP4D
