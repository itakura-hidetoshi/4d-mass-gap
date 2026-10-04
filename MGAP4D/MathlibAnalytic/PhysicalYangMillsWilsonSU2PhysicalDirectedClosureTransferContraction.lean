import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2CanonicalSelectedMarginalDirectedClosureTransfer
import MGAP4D.MathlibAnalytic.RealLinearIsometrySubspaceProjectedCompression
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalPairAsymptoticTopProjection
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalPairCompletedNonTopContraction
import Mathlib.Tactic

/-!
# Physical directed-closure SU(2) transfer with automatic unit bound

PR #5088 removes cofinality from the selected-projective-marginal transfer
route: a directed selected-cylinder family is enough to construct a bounded
operator on the selected-cylinder closure and then on the ambient continuum
L2 carrier.

This file removes the other independent input from #5088, namely the common
operator-norm bound.

At every finite scale the completed physical pair carrier is the orthogonal
sum of the completed top-top and non-top blocks.  Normalized pair transfer
fixes the top-top block, while the non-top block is a strict contraction.
Hence normalized pair transfer is contractive on the entire completed physical
pair carrier.

We therefore modify the selected-marginal compression by first projecting the
pair-Haar preimage to the completed physical pair carrier:

  J_n o S_n o P_phys o J_n^{-1} o P_range.

The existing subspace-projected-compression theorem then gives operator norm
at most one on every selected marginal, while exact action on every embedded
physical pair vector is preserved.

Directedness is already theorem-generated from the coherent readout's
eventual-support property.  Thus the only remaining model-facing H1-C3 input is

  exact cross-scale transition compatibility

for these canonical physical-carrier-projected selected operators.

Under that single compatibility input the file theorem-generates one continuum
contraction T, exact finite/continuum power intertwining on physical pair
vectors, same-subsequence strong limits T^m y for every natural time m, and
the existing q0^m bound on the nonzero norm-one continuum initial excitation.

No H1-D5 compatibility, OS/physical transfer identification, vacuum/top
alignment, or rank-one forcing is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Function Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace InnerProduct Topology

noncomputable section

local instance su2PhysicalDirectedTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance su2PhysicalDirectedCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance su2PhysicalDirectedSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance su2PhysicalDirectedMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance su2PhysicalDirectedBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance su2PhysicalDirectedSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance su2PhysicalDirectedSpatialHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance su2PhysicalDirectedNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

section FinitePhysicalContraction

private theorem norm_add_le_norm_add_of_orthogonal_right_norm_le
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (t n n' : E)
    (htn : inner ℝ t n = 0)
    (htn' : inner ℝ t n' = 0)
    (hn : ‖n'‖ ≤ ‖n‖) :
    ‖t + n'‖ ≤ ‖t + n‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [pow_two]
  rw [
    norm_add_sq_eq_norm_sq_add_norm_sq_real htn',
    norm_add_sq_eq_norm_sq_add_norm_sq_real htn]
  simpa [add_comm] using
    add_le_add_left
      (mul_self_le_mul_self (norm_nonneg n') hn)
      (‖t‖ * ‖t‖)

variable (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "PairE" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H 2
local notation "PP" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier H 2
local notation "TT" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure
    H 2 specialUnitaryTwoWilsonRankPositive beta hbeta
local notation "NN" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure
    H 2 specialUnitaryTwoWilsonRankPositive beta hbeta
local notation "R" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive beta hbeta
local notation "S₂" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive beta hbeta

/-- Normalized pair transfer is contractive on the whole completed physical
pair carrier.  The proof uses the actual completed orthogonal decomposition,
not an ambient pair-Haar contraction assertion. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_normalizedTransfer_norm_le_one
    (x : PairE) (hx : x ∈ PP) :
    ‖S₂ x‖ ≤ ‖x‖ := by
  obtain ⟨t, ht, n, hn, hsum⟩ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_exists_topTop_add_nonTop
      H 2 specialUnitaryTwoWilsonRankPositive beta hbeta x hx
  have hfix : S₂ t = t :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure_normalizedTransfer_fixed
      H 2 specialUnitaryTwoWilsonRankPositive beta hbeta t ht
  have hSn : S₂ n ∈ NN :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure_normalizedTransfer_invariant
      H 2 specialUnitaryTwoWilsonRankPositive beta hbeta hn
  have hOrtho : TT ⟂ NN :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure_isOrtho_nonTopBlockClosure
      H 2 specialUnitaryTwoWilsonRankPositive beta hbeta
  have htn : inner ℝ t n = 0 :=
    hOrtho.inner_eq ht hn
  have htSn : inner ℝ t (S₂ n) = 0 :=
    hOrtho.inner_eq ht hSn
  have hq : ‖R‖ ≤ 1 :=
    le_of_lt
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
        H 2 specialUnitaryTwoWilsonRankPositive beta hbeta)
  have hnBound0 : ‖S₂ n‖ ≤ ‖R‖ * ‖n‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure_normalizedTransfer_norm_le
      H 2 specialUnitaryTwoWilsonRankPositive beta hbeta n hn
  have hnBound : ‖S₂ n‖ ≤ ‖n‖ := by
    calc
      ‖S₂ n‖ ≤ ‖R‖ * ‖n‖ := hnBound0
      _ ≤ 1 * ‖n‖ :=
        mul_le_mul_of_nonneg_right hq (norm_nonneg n)
      _ = ‖n‖ := one_mul _
  rw [← hsum, map_add, hfix]
  exact
    norm_add_le_norm_add_of_orthogonal_right_norm_le
      t n (S₂ n) htn htSn hnBound

end FinitePhysicalContraction

section PhysicalSelectedDirected

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

local instance su2PhysicalSelectedPairCarrierCompleteSpace (n : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
        (halfExtent n) 2) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
  infer_instance

/-- Canonical selected-marginal realization of normalized pair transfer after
orthogonal projection to the completed physical pair carrier. -/
noncomputable def physicalYangMillsSU2PhysicalSelectedMarginalPairTransferOperator
    (n : ℕ) :
    Lp ℝ 2 (F.finiteMarginal (R.marginalIndex n)) →L[ℝ]
      Lp ℝ 2 (F.finiteMarginal (R.marginalIndex n)) :=
  realLinearIsometrySubspaceProjectedCompression
    (physicalYangMillsSU2PairHaarProjectiveFiniteEmbedding Q R n)
    (periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
      (halfExtent n) 2)
    (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
      (halfExtent n) 2 specialUnitaryTwoWilsonRankPositive
      (beta n) (hbeta n))

/-- On embedded physical pair vectors, the projected selected operator is
exactly the actual normalized physical pair transfer. -/
@[simp]
theorem physicalYangMillsSU2PhysicalSelectedMarginalPairTransferOperator_apply_embedding
    (n : ℕ)
    (x :
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
        (halfExtent n) 2)
    (hx :
      x ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
          (halfExtent n) 2) :
    physicalYangMillsSU2PhysicalSelectedMarginalPairTransferOperator
        Q R n
        (physicalYangMillsSU2PairHaarProjectiveFiniteEmbedding Q R n x) =
      physicalYangMillsSU2PairHaarProjectiveFiniteEmbedding Q R n
        (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
          (halfExtent n) 2 specialUnitaryTwoWilsonRankPositive
          (beta n) (hbeta n) x) := by
  unfold physicalYangMillsSU2PhysicalSelectedMarginalPairTransferOperator
  exact
    realLinearIsometrySubspaceProjectedCompression_apply_map_mem
      (physicalYangMillsSU2PairHaarProjectiveFiniteEmbedding Q R n)
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
        (halfExtent n) 2)
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
        (halfExtent n) 2 specialUnitaryTwoWilsonRankPositive
        (beta n) (hbeta n))
      x hx

/-- The selected physical operator has norm at most one; no independent
uniform-bound hypothesis is needed. -/
theorem physicalYangMillsSU2PhysicalSelectedMarginalPairTransferOperator_opNorm_le_one
    (n : ℕ) :
    ‖physicalYangMillsSU2PhysicalSelectedMarginalPairTransferOperator
        Q R n‖ ≤ 1 := by
  unfold physicalYangMillsSU2PhysicalSelectedMarginalPairTransferOperator
  apply
    realLinearIsometrySubspaceProjectedCompression_opNorm_le
      (physicalYangMillsSU2PairHaarProjectiveFiniteEmbedding Q R n)
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
        (halfExtent n) 2)
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
        (halfExtent n) 2 specialUnitaryTwoWilsonRankPositive
        (beta n) (hbeta n))
      1 zero_le_one
  intro x hx
  simpa using
    periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_normalizedTransfer_norm_le_one
      (halfExtent n) (beta n) (hbeta n) x hx

/-- Final sharpened H1-C3 input at this stage: exact cross-scale compatibility
of the canonical physical selected operators.  Directedness and the common
unit norm bound are theorem-generated. -/
structure PhysicalYangMillsSU2PhysicalSelectedMarginalPairTransferDirectedInput where
  transition_intertwines :
    ∀ {n m : ℕ}
      (h : R.marginalIndex n ⊆ R.marginalIndex m)
      (f : Lp ℝ 2 (F.finiteMarginal (R.marginalIndex n))),
      EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
          (F := F) h
          (physicalYangMillsSU2PhysicalSelectedMarginalPairTransferOperator
            Q R n f) =
        physicalYangMillsSU2PhysicalSelectedMarginalPairTransferOperator
          Q R m
          (EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
            (F := F) h f)

namespace PhysicalYangMillsSU2PhysicalSelectedMarginalPairTransferDirectedInput

variable
    (C :
      PhysicalYangMillsSU2PhysicalSelectedMarginalPairTransferDirectedInput
        Q R)

/-- The coherent readout theorem-generates directedness of the selected
marginal family. -/
theorem selectedMarginal_directed
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (G :
      PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
        S D halfExtent beta hbeta Q F R L hInvariant)
    (n m : ℕ) :
    ∃ k : ℕ,
      R.marginalIndex n ⊆ R.marginalIndex k ∧
      R.marginalIndex m ⊆ R.marginalIndex k := by
  have hn := G.marginalSupportEventually n
  have hm := G.marginalSupportEventually m
  have hBoth :
      ∀ᶠ k in atTop,
        R.marginalIndex n ⊆ R.marginalIndex k ∧
        R.marginalIndex m ⊆ R.marginalIndex k := by
    filter_upwards [hn, hm] with k hnk hmk
    exact ⟨hnk, hmk⟩
  exact hBoth.exists

/-- The generic #5088 directed system instantiated with theorem-generated
bound one. -/
noncomputable def toDirectedOperatorSystem
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (G :
      PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
        S D halfExtent beta hbeta Q F R L hInvariant) :
    EuclideanYangMillsProjectiveLimitL2DirectedOperatorSystem F L where
  marginalIndex := R.marginalIndex
  directed := selectedMarginal_directed Q R L hInvariant G
  localOperator :=
    physicalYangMillsSU2PhysicalSelectedMarginalPairTransferOperator Q R
  bound := 1
  bound_nonneg := zero_le_one
  local_norm_le := by
    intro n f
    calc
      ‖physicalYangMillsSU2PhysicalSelectedMarginalPairTransferOperator
          Q R n f‖ ≤
        ‖physicalYangMillsSU2PhysicalSelectedMarginalPairTransferOperator
          Q R n‖ * ‖f‖ :=
        (physicalYangMillsSU2PhysicalSelectedMarginalPairTransferOperator
          Q R n).le_opNorm f
      _ ≤ 1 * ‖f‖ :=
        mul_le_mul_of_nonneg_right
          (physicalYangMillsSU2PhysicalSelectedMarginalPairTransferOperator_opNorm_le_one
            Q R n)
          (norm_nonneg f)
  transition_intertwines := C.transition_intertwines

/-- The resulting continuum contraction on the selected-cylinder closure,
extended by orthogonal projection to the ambient continuum L2 carrier. -/
noncomputable def continuumTransfer
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (G :
      PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
        S D halfExtent beta hbeta Q F R L hInvariant) :
    Lp ℝ 2 L.continuumMeasure →L[ℝ]
      Lp ℝ 2 L.continuumMeasure :=
  EuclideanYangMillsProjectiveLimitL2DirectedOperatorSystem.ambientContinuumOperator
    (toDirectedOperatorSystem Q R L C hInvariant G)

theorem continuumTransfer_opNorm_le_one
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (G :
      PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
        S D halfExtent beta hbeta Q F R L hInvariant) :
    ‖continuumTransfer Q R L C hInvariant G‖ ≤ 1 := by
  simpa only [toDirectedOperatorSystem] using
    (EuclideanYangMillsProjectiveLimitL2DirectedOperatorSystem.ambientContinuumOperator_opNorm_le
      (toDirectedOperatorSystem Q R L C hInvariant G))

/-- Exact one-step finite/continuum intertwining on every physical pair vector. -/
theorem continuumTransfer_intertwines_physicalPairTransfer
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (G :
      PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
        S D halfExtent beta hbeta Q F R L hInvariant)
    (n : ℕ)
    (x :
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
        (halfExtent n) 2)
    (hx :
      x ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
          (halfExtent n) 2) :
    continuumTransfer Q R L C hInvariant G
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
  have hGeneric :=
    EuclideanYangMillsProjectiveLimitL2DirectedOperatorSystem.ambientContinuumOperator_intertwines_selected
      (toDirectedOperatorSystem Q R L C hInvariant G) n
      (physicalYangMillsSU2PairHaarProjectiveFiniteEmbedding Q R n x)
  calc
    _ =
        L.finiteMarginalL2Pullback (R.marginalIndex n)
          (physicalYangMillsSU2PhysicalSelectedMarginalPairTransferOperator
            Q R n
            (physicalYangMillsSU2PairHaarProjectiveFiniteEmbedding Q R n x)) := by
      simpa only [toDirectedOperatorSystem] using hGeneric
    _ = _ := by
      rw [
        physicalYangMillsSU2PhysicalSelectedMarginalPairTransferOperator_apply_embedding
          Q R n x hx]

/-- Exact power intertwining follows because the physical pair carrier is
invariant under normalized pair transfer. -/
theorem continuumTransfer_pow_intertwines_physicalPairTransfer
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (G :
      PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
        S D halfExtent beta hbeta Q F R L hInvariant)
    (n m : ℕ)
    (x :
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
        (halfExtent n) 2)
    (hx :
      x ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
          (halfExtent n) 2) :
    (continuumTransfer Q R L C hInvariant G ^ m)
        (physicalYangMillsSU2PairHaarProjectiveContinuumEmbedding
          Q R L n x) =
      physicalYangMillsSU2PairHaarProjectiveContinuumEmbedding
        Q R L n
        ((periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
          (halfExtent n) 2 specialUnitaryTwoWilsonRankPositive
          (beta n) (hbeta n) ^ m) x) := by
  let T := continuumTransfer Q R L C hInvariant G
  let Sn :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
      (halfExtent n) 2 specialUnitaryTwoWilsonRankPositive
      (beta n) (hbeta n)
  let J :=
    physicalYangMillsSU2PairHaarProjectiveContinuumEmbedding Q R L n
  change (T ^ m) (J x) = J ((Sn ^ m) x)
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
      have hxS :
          Sn x ∈
            periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
              (halfExtent n) 2 := by
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_normalizedTransfer_invariant
            (halfExtent n) 2 specialUnitaryTwoWilsonRankPositive
            (beta n) (hbeta n) hx
      change (T ^ m) (T (J x)) = J ((Sn ^ m) (Sn x))
      have hstep : T (J x) = J (Sn x) := by
        simpa [T, Sn, J] using
          continuumTransfer_intertwines_physicalPairTransfer
            Q R L C hInvariant G n x hx
      rw [hstep]
      exact ih (Sn x) hxS

/-- The theorem-generated nonzero continuum initial excitation has
same-subsequence evolved strong limits under one continuum contraction and
retains the uniform q0^m bound. -/
theorem
    physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_continuumDiscreteTime_q0
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
              (𝓝 ((continuumTransfer Q R L C hInvariant G ^ m) y)) ∧
            ‖(continuumTransfer Q R L C hInvariant G ^ m) y‖ ≤
              GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ m := by
  obtain ⟨phi, hphi, cInf, hcInf, hInitial, hyNorm⟩ :=
    physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_projective_strong_limit
      Q R L hInvariant G
  let y :=
    physicalYangMillsSU2ThreeModeContinuumSynthesis
      Q R L hInvariant G cInf
  refine ⟨phi, hphi, y, by simpa [y] using hyNorm, ?_⟩
  intro m
  have hPow :
      Tendsto
        (fun j =>
          (continuumTransfer Q R L C hInvariant G ^ m)
            (physicalYangMillsSU2PairHaarProjectiveContinuumEmbedding
              Q R L (phi j)
              (physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice
                Q hInvariant (phi j))))
        atTop
        (𝓝 ((continuumTransfer Q R L C hInvariant G ^ m) y)) := by
    have hMap :=
      (((continuumTransfer Q R L C hInvariant G ^ m).continuous.tendsto y).comp
        hInitial)
    simpa [y] using hMap
  have hStrong :
      Tendsto
        (fun j =>
          physicalYangMillsVacuumNormalizedSU2ThreeModeEvolvedProjectiveContinuumImage
            Q R L hInvariant (phi j) m)
        atTop
        (𝓝 ((continuumTransfer Q R L C hInvariant G ^ m) y)) := by
    apply hPow.congr'
    exact Filter.Eventually.of_forall fun j => by
      unfold
        physicalYangMillsVacuumNormalizedSU2ThreeModeEvolvedProjectiveContinuumImage
      exact
        continuumTransfer_pow_intertwines_physicalPairTransfer
          Q R L C hInvariant G (phi j) m
          (physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice
            Q hInvariant (phi j))
          (physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_mem_physicalPairCarrier
            Q hInvariant (phi j))
  refine ⟨hStrong, ?_⟩
  exact
    physicalYangMillsVacuumNormalizedSU2ThreeModeEvolvedProjectiveStrongLimit_norm_le_uniform_q0
      Q R L hInvariant s hs hcut phi m
      ((continuumTransfer Q R L C hInvariant G ^ m) y)
      hStrong

theorem continuumTransfer_pow_add_apply
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (G :
      PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
        S D halfExtent beta hbeta Q F R L hInvariant)
    (m k : ℕ)
    (y : Lp ℝ 2 L.continuumMeasure) :
    (continuumTransfer Q R L C hInvariant G ^ (m + k)) y =
      (continuumTransfer Q R L C hInvariant G ^ m)
        ((continuumTransfer Q R L C hInvariant G ^ k) y) := by
  rw [pow_add]
  rfl

end PhysicalYangMillsSU2PhysicalSelectedMarginalPairTransferDirectedInput

end PhysicalSelectedDirected

end

end MathlibAnalytic
end MGAP4D
