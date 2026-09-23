import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaZeroGroundStateSixSpatialProductHaarCommonFixedBoundary
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialRandomScanRayleigh
import Mathlib.Tactic

/-!
# Exact beta-zero six-spatial pair-Haar Rayleigh constant

For a pairwise commuting family of self-adjoint idempotents, the ordered
sweep is itself a self-adjoint idempotent.  Applying this to the actual
beta-zero Wilson six-spatial pair-Haar family and using the already identified
common-fixed sector gives an explicit frame constant on the orthogonal
complement of the complete left-boundary L2 subspace.

The resulting constants are exact for this argument:

* frame coefficient kappa_0 = 1/6;
* random-scan Rayleigh factor q_0 = 5/6.

No positive-beta continuity statement is made here.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped BigOperators InnerProductSpace InnerProduct

noncomputable section

local instance betaZeroPairHaarRayleighTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance betaZeroPairHaarRayleighCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance betaZeroPairHaarRayleighSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance betaZeroPairHaarRayleighMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance betaZeroPairHaarRayleighBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance betaZeroPairHaarRayleighSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- An ordered sweep of pairwise commuting idempotents is idempotent. -/
theorem realHilbertProjectionSweep_idempotent_of_pairwise_commute
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (P : C → E →L[ℝ] E)
    (hIdem : ∀ c : C, (P c).comp (P c) = P c)
    (hComm : ∀ (c d : C) (x : E), P c (P d x) = P d (P c x))
    (cs : List C) :
    (realHilbertProjectionSweep P cs).comp
        (realHilbertProjectionSweep P cs) =
      realHilbertProjectionSweep P cs := by
  induction cs with
  | nil =>
      simp [realHilbertProjectionSweep]
  | cons c cs ih =>
      apply ContinuousLinearMap.ext
      intro x
      simp only [realHilbertProjectionSweep, ContinuousLinearMap.comp_apply]
      have hcc : P c (P c x) = P c x := by
        have h := congrArg (fun Q : E →L[ℝ] E => Q x) (hIdem c)
        simpa using h
      have htail :
          realHilbertProjectionSweep P cs
              (realHilbertProjectionSweep P cs (P c x)) =
            realHilbertProjectionSweep P cs (P c x) := by
        have h := congrArg
          (fun Q : E →L[ℝ] E => Q (P c x)) ih
        simpa using h
      calc
        realHilbertProjectionSweep P cs
            (P c (realHilbertProjectionSweep P cs (P c x))) =
          realHilbertProjectionSweep P cs
            (realHilbertProjectionSweep P cs (P c (P c x))) := by
              rw [realHilbertProjectionSweep_commute P hComm c cs (P c x)]
        _ = realHilbertProjectionSweep P cs
            (realHilbertProjectionSweep P cs (P c x)) := by
              rw [hcc]
        _ = realHilbertProjectionSweep P cs (P c x) := htail

/-- An ordered sweep of pairwise commuting symmetric maps is symmetric. -/
theorem realHilbertProjectionSweep_symmetric_of_pairwise_commute
    {E C : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (P : C → E →L[ℝ] E)
    (hSymm : ∀ (c : C) (x y : E),
      inner ℝ (P c x) y = inner ℝ x (P c y))
    (hComm : ∀ (c d : C) (x : E), P c (P d x) = P d (P c x))
    (cs : List C)
    (x y : E) :
    inner ℝ (realHilbertProjectionSweep P cs x) y =
      inner ℝ x (realHilbertProjectionSweep P cs y) := by
  induction cs generalizing x y with
  | nil =>
      simp [realHilbertProjectionSweep]
  | cons c cs ih =>
      simp only [realHilbertProjectionSweep, ContinuousLinearMap.comp_apply]
      calc
        inner ℝ (realHilbertProjectionSweep P cs (P c x)) y =
            inner ℝ (P c x) (realHilbertProjectionSweep P cs y) :=
          ih (P c x) y
        _ = inner ℝ x (P c (realHilbertProjectionSweep P cs y)) :=
          hSymm c x (realHilbertProjectionSweep P cs y)
        _ = inner ℝ x (realHilbertProjectionSweep P cs (P c y)) := by
          rw [realHilbertProjectionSweep_commute P hComm c cs y]

/-- The actual beta-zero six-spatial pair-Haar full sweep is idempotent. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarFullSweep_idempotent
    (H N : ℕ) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarFullSweep
      H N).comp
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarFullSweep
        H N) =
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarFullSweep
      H N := by
  exact
    realHilbertProjectionSweep_idempotent_of_pairwise_commute
      (fun c =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection
          H N c)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection_idempotent
        H N)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection_commute
        H N)
      ((Finset.univ : Finset (Fin 6)).toList)

/-- The actual beta-zero six-spatial pair-Haar full sweep is symmetric. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarFullSweep_symmetric
    (H N : ℕ)
    (x y :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarFullSweep
          H N x) y =
      inner ℝ x
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarFullSweep
          H N y) := by
  exact
    realHilbertProjectionSweep_symmetric_of_pairwise_commute
      (fun c =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection
          H N c)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection_symmetric
        H N)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection_commute
        H N)
      ((Finset.univ : Finset (Fin 6)).toList)
      x y

/-- On the orthogonal complement of the complete left-boundary L2 sector,
the actual beta-zero six-spatial full sweep vanishes. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarFullSweep_eq_zero_of_mem_fst_orthogonal
    (H N : ℕ)
    (x :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N)
    (hx : x ∈
      (lpMeas ℝ ℝ
        (MeasurableSpace.comap Prod.fst
          (inferInstance : MeasurableSpace
            (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)))
        2
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N))ᗮ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarFullSweep
        H N x = 0 := by
  let S :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarFullSweep
      H N
  have hSfix : S (S x) = S x := by
    have h := congrArg
      (fun Q :
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N →L[ℝ]
          PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N =>
        Q x)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarFullSweep_idempotent
        H N)
    simpa [S] using h
  have hSmem :
      S x ∈ lpMeas ℝ ℝ
        (MeasurableSpace.comap Prod.fst
          (inferInstance : MeasurableSpace
            (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)))
        2
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarFullSweep_eq_self_iff_mem_fst
        H N (S x)).1 hSfix
  have hxOrth := hx
  rw [Submodule.mem_orthogonal] at hxOrth
  have hOrth : inner ℝ (S x) x = 0 :=
    hxOrth (S x) hSmem
  have hSelf : inner ℝ (S x) (S x) = 0 := by
    calc
      inner ℝ (S x) (S x) = inner ℝ x (S (S x)) :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarFullSweep_symmetric
          H N x (S x)
      _ = inner ℝ x (S x) := by rw [hSfix]
      _ = inner ℝ (S x) x := real_inner_comm _ _
      _ = 0 := hOrth
  have hnormSq : ‖S x‖ ^ 2 = 0 := by
    rw [← real_inner_self_eq_norm_sq]
    exact hSelf
  have hnorm : ‖S x‖ = 0 := by
    nlinarith [norm_nonneg (S x)]
  exact norm_eq_zero.mp hnorm

/-- Exact beta-zero six-spatial frame coefficient on the complement of the
common fixed boundary sector: kappa_0 = 1/6. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaar_frame_one_six_of_mem_fst_orthogonal
    (H N : ℕ)
    (hN : 0 < N)
    (x :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N)
    (hx : x ∈
      (lpMeas ℝ ℝ
        (MeasurableSpace.comap Prod.fst
          (inferInstance : MeasurableSpace
            (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)))
        2
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N))ᗮ) :
    (1 / 6 : ℝ) * ‖x‖ ^ 2 ≤
      groundStateJointColorNormalizedResidualEnergy
        (fun c =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection
            H N c)
        x := by
  have hten :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarFullSweep_tensorization
      H N x
  have hzero :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarFullSweep_eq_zero_of_mem_fst_orthogonal
      H N x hx
  rw [hzero, sub_zero] at hten
  have hscaled :=
    mul_le_mul_of_nonneg_left hten (show 0 ≤ (1 / 6 : ℝ) by norm_num)
  simpa [groundStateJointColorNormalizedResidualEnergy] using hscaled

/-- Literal beta-zero random-scan operator for the six pair-Haar spatial
projections. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarRandomScan
    (H N : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N :=
  groundStateJointColorRandomScanOperator
    (fun c =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection
        H N c)

/-- Exact beta-zero six-spatial random-scan Rayleigh contraction on the
orthogonal complement of the common fixed boundary sector: q_0 = 5/6. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarRandomScan_rayleigh_five_six_of_mem_fst_orthogonal
    (H N : ℕ)
    (hN : 0 < N)
    (x :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N)
    (hx : x ∈
      (lpMeas ℝ ℝ
        (MeasurableSpace.comap Prod.fst
          (inferInstance : MeasurableSpace
            (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)))
        2
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N))ᗮ) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarRandomScan
          H N x)
        x ≤
      (5 / 6 : ℝ) * ‖x‖ ^ 2 := by
  have hframe :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaar_frame_one_six_of_mem_fst_orthogonal
      H N hN x hx
  have hRayleigh :=
    (groundStateJointColorFrame_iff_randomScanRayleigh_le
      (fun c =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection
          H N c)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection_idempotent
        H N)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection_symmetric
        H N)
      (1 / 6 : ℝ)
      x).1 hframe
  have hcoeff : (1 - (6 : ℝ)⁻¹) = (5 / 6 : ℝ) := by
    norm_num
  rw [← hcoeff]
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarRandomScan] using
      hRayleigh

end

end MGAP4D.MathlibAnalytic
