import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaZeroPhysicalSixSpatialExactFrameRayleigh
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateSixSpatialMeanProjectionGap
import Mathlib.Tactic

/-!
# Beta-zero genuine ground-state / literal pair-Haar six-spatial transport

This unit transports the exact beta-zero literal pair-Haar six-spatial frame
constant back to the proof-indexed genuine ground-state joint carrier consumed
by the physical transfer-gap receiver.

The transport is intentionally narrow:

* cast real L2 vectors only along exact measure equalities;
* prove that conditional expectation commutes with this exact measure cast;
* prove that the genuine beta-zero right-boundary lift of the ground-state
  transform becomes the literal pair-Haar right-boundary pullback;
* transport the six projected squared norms term-by-term;
* feed q_0 = 5/6 into the existing genuine mean-projection receiver.

No positive-beta comparison and no new probability geometry are introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped BigOperators InnerProductSpace InnerProduct

noncomputable section

local instance betaZeroGenuinePairHaarTransportTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance betaZeroGenuinePairHaarTransportCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance betaZeroGenuinePairHaarTransportSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance betaZeroGenuinePairHaarTransportMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance betaZeroGenuinePairHaarTransportBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance betaZeroGenuinePairHaarTransportSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Exact cast between real L2 carriers when the underlying measures are
literally equal.  Keeping this as a small helper prevents dependent Lp
rewrites from spreading through model-facing proofs. -/
noncomputable def realL2CastOfMeasureEq
    {α : Type*}
    [MeasurableSpace α]
    {μ ν : Measure α}
    (hμν : μ = ν) :
    Lp ℝ 2 μ → Lp ℝ 2 ν :=
  fun f =>
    match hμν with
    | rfl => f

@[simp] theorem realL2CastOfMeasureEq_rfl
    {α : Type*}
    [MeasurableSpace α]
    (μ : Measure α)
    (f : Lp ℝ 2 μ) :
    realL2CastOfMeasureEq (rfl : μ = μ) f = f := by
  rfl

theorem realL2CastOfMeasureEq_norm
    {α : Type*}
    [MeasurableSpace α]
    {μ ν : Measure α}
    (hμν : μ = ν)
    (f : Lp ℝ 2 μ) :
    ‖realL2CastOfMeasureEq hμν f‖ = ‖f‖ := by
  cases hμν
  rfl

theorem realL2CastOfMeasureEq_inner
    {α : Type*}
    [MeasurableSpace α]
    {μ ν : Measure α}
    (hμν : μ = ν)
    (f g : Lp ℝ 2 μ) :
    inner ℝ
        (realL2CastOfMeasureEq hμν f)
        (realL2CastOfMeasureEq hμν g) =
      inner ℝ f g := by
  cases hμν
  rfl

theorem realL2CastOfMeasureEq_coeFn
    {α : Type*}
    [MeasurableSpace α]
    {μ ν : Measure α}
    (hμν : μ = ν)
    (f : Lp ℝ 2 μ) :
    (realL2CastOfMeasureEq hμν f : α → ℝ) =ᵐ[ν]
      (f : α → ℝ) := by
  cases hμν
  exact Filter.Eventually.of_forall fun _ => rfl

/-- Exact measure casts commute with L2 conditional expectation once both
the retained and ambient measurable spaces are supplied explicitly. -/
theorem realL2CastOfMeasureEq_condExpL2
    {α : Type*}
    [m0 : MeasurableSpace α]
    {m : MeasurableSpace α}
    (hm : m ≤ m0)
    {μ ν : Measure α}
    (hμν : μ = ν)
    (f : Lp ℝ 2 μ) :
    realL2CastOfMeasureEq hμν
        ((condExpL2 (m := m) (m0 := m0) ℝ ℝ hm) f) =
      ((condExpL2 (m := m) (m0 := m0) ℝ ℝ hm)
        (realL2CastOfMeasureEq hμν f) : Lp ℝ 2 ν) := by
  cases hμν
  rfl

/-- Exact casts commute with pullback along a measure-preserving map when both
source and target measures are identified by equality. -/
theorem realL2CastOfMeasureEq_compMeasurePreserving
    {α β : Type*}
    [MeasurableSpace α]
    [MeasurableSpace β]
    {μα να : Measure α}
    {μβ νβ : Measure β}
    (hα : μα = να)
    (hβ : μβ = νβ)
    (φ : α → β)
    (hmp : MeasurePreserving φ μα μβ)
    (hmp' : MeasurePreserving φ να νβ)
    (f : Lp ℝ 2 μβ) :
    realL2CastOfMeasureEq hα
        (Lp.compMeasurePreservingₗᵢ ℝ φ hmp f) =
      Lp.compMeasurePreservingₗᵢ ℝ φ hmp'
        (realL2CastOfMeasureEq hβ f) := by
  cases hα
  cases hβ
  have hproof : hmp = hmp' := Subsingleton.elim _ _
  cases hproof
  rfl

/-- The genuine beta-zero vacuum L2 carrier cast to literal spatial Haar L2. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroVacuumToHaarL2
    (H N : ℕ)
    (hN : 0 < N)
    (u :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateVacuumL2
        H N hN 0 (by norm_num)) :
    Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) :=
  realL2CastOfMeasureEq
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure_zero_eq_Haar
      H N hN)
    u

/-- The genuine beta-zero joint L2 carrier cast to literal pair-Haar L2. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroJointToPairHaarL2
    (H N : ℕ)
    (hN : 0 < N)
    (z :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN 0 (by norm_num)) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N :=
  realL2CastOfMeasureEq
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_zero_eq_pairHaar
      H N hN)
    z

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroJointToPairHaarL2_norm
    (H N : ℕ)
    (hN : 0 < N)
    (z :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN 0 (by norm_num)) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroJointToPairHaarL2
        H N hN z‖ = ‖z‖ := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroJointToPairHaarL2
  exact
    realL2CastOfMeasureEq_norm
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_zero_eq_pairHaar
        H N hN)
      z

/-- At beta zero the ground-state transform becomes the identity after the
exact vacuum-measure cast. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroVacuumToHaarL2_haarToVacuum
    (H N : ℕ)
    (hN : 0 < N)
    (f :
      Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroVacuumToHaarL2
        H N hN
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry
          H N hN 0 (by norm_num) f) =
      f := by
  let μ :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let ν :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
      H N hN 0 (by norm_num)
  let U :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry
      H N hN 0 (by norm_num)
  have hνμ : ν = μ := by
    simpa [ν, μ] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure_zero_eq_Haar
        H N hN
  have hCast :
      (realL2CastOfMeasureEq hνμ (U f) :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ) =ᵐ[μ]
      (U f :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ) :=
    realL2CastOfMeasureEq_coeFn hνμ (U f)
  have hUν :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2_coeFn
      H N hN 0 (by norm_num) f
  have hUμ :
      (U f :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ) =ᵐ[μ]
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumFunction
        H N hN 0 (by norm_num) f := by
    rw [← hνμ]
    simpa [U, ν] using hUν
  have hOne :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_zero_coeFn_ae_eq_one
      H N hN
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroVacuumToHaarL2
  apply Lp.ext
  filter_upwards [hCast, hUμ, hOne] with A hCastA hUA hOneA
  rw [hCastA, hUA]
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumFunction
  rw [hOneA]
  simp

/-- After the exact beta-zero measure casts, the genuine right-boundary lift
is the literal pair-Haar right-coordinate pullback. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroJointToPairHaarL2_rightBoundary
    (H N : ℕ)
    (hN : 0 < N)
    (u :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateVacuumL2
        H N hN 0 (by norm_num)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroJointToPairHaarL2
        H N hN
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift
          H N hN 0 (by norm_num) u) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPairHaarRightBoundaryL2Isometry
        H N
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroVacuumToHaarL2
          H N hN u) := by
  let hJoint :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_zero_eq_pairHaar
      H N hN
  let hVac :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure_zero_eq_Haar
      H N hN
  have hTransport :=
    realL2CastOfMeasureEq_compMeasurePreserving
      hJoint hVac Prod.snd
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_snd_measurePreserving
        H N hN 0 (by norm_num))
      (MeasureTheory.measurePreserving_snd
        (μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
        (ν := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
      u
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroJointToPairHaarL2,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroVacuumToHaarL2,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPairHaarRightBoundaryL2Isometry,
    hJoint, hVac] using hTransport

/-- The exact beta-zero joint cast intertwines every genuine six-spatial
conditional expectation with its literal pair-Haar projection. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroJointToPairHaarL2_sixSpatialCondExp
    (H N : ℕ)
    (hN : 0 < N)
    (c : Fin 6)
    (z :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN 0 (by norm_num)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroJointToPairHaarL2
        H N hN
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialCondExpL2
          H N hN 0 (by norm_num) c z) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection
        H N c
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroJointToPairHaarL2
          H N hN z) := by
  let color := periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c
  let hJoint :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_zero_eq_pairHaar
      H N hN
  change
    realL2CastOfMeasureEq hJoint
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2
          H N hN 0 (by norm_num) color z) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorPairHaarProjection
        H N color
        (realL2CastOfMeasureEq hJoint z)
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2_apply,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorPairHaarProjection_apply]
  exact
    realL2CastOfMeasureEq_condExpL2
      (m0 := (Prod.instMeasurableSpace :
        MeasurableSpace
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)))
      (m :=
        periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
          H N color)
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace_le
        H N color)
      hJoint z

/-- The mean retained squared norm of the genuine beta-zero six-spatial
family is exactly the literal pair-Haar mean after the joint cast. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZero_sixSpatialMeanProjectedNormSq_cast
    (H N : ℕ)
    (hN : 0 < N)
    (z :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN 0 (by norm_num)) :
    groundStateJointColorMeanProjectedNormSq
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialCondExpL2
          H N hN 0 (by norm_num))
        z =
      groundStateJointColorMeanProjectedNormSq
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection
          H N)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroJointToPairHaarL2
          H N hN z) := by
  unfold groundStateJointColorMeanProjectedNormSq
  congr 1
  apply Finset.sum_congr rfl
  intro c _hc
  have hnorm :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroJointToPairHaarL2_norm
      H N hN
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialCondExpL2
        H N hN 0 (by norm_num) c z)
  have hintertwine :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroJointToPairHaarL2_sixSpatialCondExp
      H N hN c z
  calc
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialCondExpL2
        H N hN 0 (by norm_num) c z‖ ^ 2 =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroJointToPairHaarL2
          H N hN
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialCondExpL2
            H N hN 0 (by norm_num) c z)‖ ^ 2 := by
        rw [hnorm]
    _ =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection
          H N c
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroJointToPairHaarL2
            H N hN z)‖ ^ 2 := by
        rw [hintertwine]

/-- On a genuine physical beta-zero top-orthogonal vector, the genuine
six-spatial mean projected squared norm has the exact contraction q_0 = 5/6. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPhysicalSixSpatialMeanProjection_five_six
    (H N : ℕ)
    (hN : 0 < N)
    (x :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN 0 (by norm_num)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialMeanProjectedNormSq
        H N hN 0 (by norm_num)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry
          H N hN 0 (by norm_num)
          (((x :
            periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
              H N) :
            Lp ℝ 2
              (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)))) ≤
      (5 / 6 : ℝ) *
        ‖(x :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
            H N)‖ ^ 2 := by
  let f :
      Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) :=
    ((x :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
        H N) :
      Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
  let U :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry
      H N hN 0 (by norm_num)
  let R :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift
      H N hN 0 (by norm_num)
  let z :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPhysicalPairHaarBoundaryVector
      H N hN x
  have hUcast :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroVacuumToHaarL2
          H N hN (U f) = f := by
    simpa [U, f] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroVacuumToHaarL2_haarToVacuum
        H N hN f
  have hRcast :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroJointToPairHaarL2
          H N hN (R (U f)) = z := by
    calc
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroJointToPairHaarL2
          H N hN (R (U f)) =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPairHaarRightBoundaryL2Isometry
          H N
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroVacuumToHaarL2
            H N hN (U f)) := by
              simpa [R] using
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroJointToPairHaarL2_rightBoundary
                  H N hN (U f)
      _ =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPairHaarRightBoundaryL2Isometry
          H N f := by rw [hUcast]
      _ = z := by
        rfl
  have hMeanCast :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZero_sixSpatialMeanProjectedNormSq_cast
      H N hN (R (U f))
  have hMeanTransport :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialMeanProjectedNormSq
          H N hN 0 (by norm_num) (U f) =
        groundStateJointColorMeanProjectedNormSq
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection
            H N)
          z := by
    simpa [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialMeanProjectedNormSq,
      R, hRcast] using hMeanCast
  have hFramePhysical :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPhysicalSixSpatialPairHaar_frame_one_six
      H N hN x
  have hFrameZ :
      (1 / 6 : ℝ) * ‖z‖ ^ 2 ≤
        groundStateJointColorNormalizedResidualEnergy
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection
            H N)
          z := by
    simpa [z] using hFramePhysical
  have hMeanZ :=
    (groundStateJointColorFrame_iff_meanProjectedNormSq_le
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection
        H N)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection_idempotent
        H N)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection_symmetric
        H N)
      (1 / 6 : ℝ)
      z).1 hFrameZ
  have hCoeff : (1 - (1 / 6 : ℝ)) = (5 / 6 : ℝ) := by
    norm_num
  rw [hCoeff] at hMeanZ
  rw [hMeanTransport]
  simpa [z] using hMeanZ

/-- The beta-zero six-spatial route gives the receiver consistency bound
1/16 for the genuine physical transfer gap.  The exact independent endpoint
remains gap(0) = 1. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroSixSpatialRoute_transferGap_one_sixteen
    (H N : ℕ)
    (hN : 0 < N) :
    (1 / 16 : ℝ) ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
        H N hN 0 (by norm_num) := by
  have hGap :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialMeanProjectionContraction_implies_transferGap
      H N hN 0 (by norm_num)
      (5 / 6 : ℝ)
      (by norm_num)
      (by norm_num)
      (fun x =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPhysicalSixSpatialMeanProjection_five_six
          H N hN x)
  have hcoeff :
      3 * (1 - (5 / 6 : ℝ)) / 8 = (1 / 16 : ℝ) := by
    norm_num
  rw [← hcoeff]
  exact hGap

/-- Consistency package: the six-spatial receiver yields 1/16, while the
independently proved exact beta-zero physical transfer gap remains one. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroSixSpatialRoute_consistent_with_exact_gap
    (H N : ℕ)
    (hN : 0 < N) :
    ((1 / 16 : ℝ) ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
        H N hN 0 (by norm_num)) ∧
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
        H N hN 0 (by norm_num) = 1 := by
  exact ⟨
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroSixSpatialRoute_transferGap_one_sixteen
      H N hN,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap_zero
      H N hN⟩

end

end MGAP4D.MathlibAnalytic
