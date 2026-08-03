import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCanonicalBoundaryBetaZeroNormalization
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCanonicalBoundaryHeatBathSemigroupDefectPackage
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathProjectionL2Identification
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroCoordinateProjectionCommutationBCF
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped BigOperators

noncomputable section

local instance canonicalBoundaryBetaZeroInvarianceNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance canonicalBoundaryBetaZeroInvarianceTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance canonicalBoundaryBetaZeroInvarianceCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance canonicalBoundaryBetaZeroInvarianceSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance canonicalBoundaryBetaZeroInvarianceMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance canonicalBoundaryBetaZeroInvarianceBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance canonicalBoundaryBetaZeroInvarianceBoundaryHaarProbability
    (H N : ℕ) :
    IsProbabilityMeasure (periodicHypercubicEvenBoundaryHaarMeasure H N) := by
  unfold periodicHypercubicEvenBoundaryHaarMeasure
  unfold FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure
  infer_instance

local instance canonicalBoundaryBetaZeroInvarianceBoundaryHaarWeaklyRegular
    (H N : ℕ) :
    (periodicHypercubicEvenBoundaryHaarMeasure H N).WeaklyRegular := by
  unfold periodicHypercubicEvenBoundaryHaarMeasure
  unfold FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure
  infer_instance

private theorem memLp_two_of_stronglyMeasurable_uniform_bound
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    (f : α → ℝ)
    (hf : StronglyMeasurable f)
    (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ x, |f x| ≤ M) :
    MemLp f 2 μ := by
  apply (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).2
  have hsq : StronglyMeasurable (fun x => f x ^ 2) := by
    simpa [pow_two] using hf.mul hf
  apply Integrable.of_bound hsq.aestronglyMeasurable (M ^ 2)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_pow]
  nlinarith [abs_nonneg (f x), hM x]

/-- A canonical full configuration with prescribed shared-boundary data and
identity values on both open halves. -/
noncomputable def periodicHypercubicEvenCanonicalBoundarySection
    (H N : ℕ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ :=
  ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedPiMeasurableEquiv
    (Matrix.specialUnitaryGroup (Fin N) ℂ)).symm
      (b, (fun _ => 1, fun _ => 1))

/-- The canonical section has exactly the prescribed boundary restriction. -/
@[simp] theorem periodicHypercubicEvenCanonicalBoundarySection_boundaryRestriction
    (H N : ℕ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    (periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction
        (periodicHypercubicEvenCanonicalBoundarySection H N b) = b := by
  let Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ
  let P := periodicHypercubicEvenEdgeOrbitPartition H
  let z : P.BoundaryConfiguration Gauge ×
      (P.OpenHalfConfiguration Gauge × P.OpenHalfConfiguration Gauge) :=
    (b, (fun _ => 1, fun _ => 1))
  have hcoords :
      P.boundaryFiberedCoordinates Gauge
          ((P.boundaryFiberedPiMeasurableEquiv Gauge).symm z) = z := by
    rw [← P.boundaryFiberedPiMeasurableEquiv_apply]
    exact (P.boundaryFiberedPiMeasurableEquiv Gauge).apply_symm_apply z
  have hfirst := congrArg Prod.fst hcoords
  simpa [periodicHypercubicEvenCanonicalBoundarySection, z, P, Gauge,
    FiniteInvolutiveEdgeOrbitPartition.boundaryFiberedCoordinates] using hfirst

/-- The canonical boundary section is measurable. -/
theorem periodicHypercubicEvenCanonicalBoundarySection_measurable
    (H N : ℕ) :
    Measurable (periodicHypercubicEvenCanonicalBoundarySection H N) := by
  change Measurable (fun b =>
    ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedPiMeasurableEquiv
      (Matrix.specialUnitaryGroup (Fin N) ℂ)).symm
        (b, (fun _ => 1, fun _ => 1)))
  exact
    ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedPiMeasurableEquiv
      (Matrix.specialUnitaryGroup (Fin N) ℂ)).symm.measurable.comp
        (measurable_id.prodMk (measurable_const.prodMk measurable_const))

/-- Pull a bounded continuous boundary observable back to the full finite
configuration space. -/
noncomputable def periodicHypercubicEvenBoundaryBCFPullback
    (H N : ℕ)
    (f : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) ℝ) :
    BoundedContinuousFunction
      (PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ) ℝ :=
  f.compContinuous
    { toFun := (periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction
      continuous_toFun := by
        apply continuous_pi
        intro e
        exact continuous_apply e.1 }

@[simp] theorem periodicHypercubicEvenBoundaryBCFPullback_apply
    (H N : ℕ)
    (f : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) ℝ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenBoundaryBCFPullback H N f A =
      f ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction A) :=
  rfl

/-- Replacing a non-boundary physical link leaves the shared-boundary
restriction unchanged. -/
theorem periodicHypercubicEvenBoundaryRestriction_replaceLink_eq_self_of_ne_fixed
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (target : PeriodicHypercubicEvenEdge H)
    (hTarget : periodicHypercubicEvenEdgeSide H target ≠
      ReflectionEdgeSide.fixed)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN 0 (by norm_num)).base.replaceLink
          A target g) =
      (periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction A := by
  funext e
  have hne : e.1 ≠ target := by
    intro heq
    subst target
    exact hTarget e.2
  unfold FiniteInvolutiveEdgeOrbitPartition.boundaryRestriction
  exact compact_oriented_replaceLink_other
    (L := (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN 0 (by norm_num)).base)
    (A := A) (target := target) (e := e.1) (g := g) hne

/-- If two full configurations have the same shared boundary, replacing the
same fixed boundary link by the same group element preserves that equality. -/
theorem periodicHypercubicEvenBoundaryRestriction_replaceLink_eq_of_eq
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (target : PeriodicHypercubicEvenEdge H)
    (_hTarget : periodicHypercubicEvenEdgeSide H target =
      ReflectionEdgeSide.fixed)
    (A B : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hAB :
      (periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction A =
        (periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction B)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN 0 (by norm_num)).base.replaceLink
          A target g) =
      (periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN 0 (by norm_num)).base.replaceLink
          B target g) := by
  funext e
  unfold FiniteInvolutiveEdgeOrbitPartition.boundaryRestriction
  by_cases he : e.1 = target
  · subst target
    simp
  · rw [compact_oriented_replaceLink_other
      (L := (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN 0 (by norm_num)).base)
      (A := A) (target := target) (e := e.1) (g := g) he,
      compact_oriented_replaceLink_other
      (L := (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN 0 (by norm_num)).base)
      (A := B) (target := target) (e := e.1) (g := g) he]
    simpa [FiniteInvolutiveEdgeOrbitPartition.boundaryRestriction] using
      congrFun hAB e

/-- Boundary representative obtained after applying one concrete beta-zero
one-link heat-bath projection to the full pullback and evaluating on the
canonical section. -/
noncomputable def periodicHypercubicEvenBoundaryProjectedBCFFunction
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (target : PeriodicHypercubicEvenEdge H)
    (f : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) ℝ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) : ℝ :=
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN 0 (by norm_num)
  C.singleLinkHeatBathProjection target
    (periodicHypercubicEvenBoundaryBCFPullback H N f)
    (periodicHypercubicEvenCanonicalBoundarySection H N b)

/-- The projected boundary representative is strongly measurable. -/
theorem periodicHypercubicEvenBoundaryProjectedBCFFunction_stronglyMeasurable
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (target : PeriodicHypercubicEvenEdge H)
    (f : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) ℝ) :
    StronglyMeasurable
      (periodicHypercubicEvenBoundaryProjectedBCFFunction
        H N hN target f) := by
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN 0 (by norm_num)
  let O := periodicHypercubicEvenBoundaryBCFPullback H N f
  have hP : StronglyMeasurable (C.singleLinkHeatBathProjection target O) :=
    continuous_compact_oriented_singleLinkHeatBathProjection_stronglyMeasurable
      C target O O.continuous.stronglyMeasurable
  have hs := periodicHypercubicEvenCanonicalBoundarySection_measurable H N
  exact (hP.measurable.comp hs).stronglyMeasurable

/-- Uniform bound for the projected boundary representative. -/
theorem periodicHypercubicEvenBoundaryProjectedBCFFunction_abs_le
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (target : PeriodicHypercubicEvenEdge H)
    (f : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) ℝ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    |periodicHypercubicEvenBoundaryProjectedBCFFunction
      H N hN target f b| ≤ ‖f‖ := by
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN 0 (by norm_num)
  let O := periodicHypercubicEvenBoundaryBCFPullback H N f
  have hO : ∀ A, |O A| ≤ ‖f‖ := by
    intro A
    simpa [O, periodicHypercubicEvenBoundaryBCFPullback] using
      f.norm_coe_le_norm
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction A)
  exact
    continuous_compact_oriented_singleLinkHeatBathProjection_abs_le
      C target O O.continuous.stronglyMeasurable ‖f‖ (norm_nonneg _) hO
      (periodicHypercubicEvenCanonicalBoundarySection H N b)

/-- The projected boundary representative defines a genuine boundary Haar
`L²` vector. -/
noncomputable def periodicHypercubicEvenBoundaryProjectedBCFL2
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (target : PeriodicHypercubicEvenEdge H)
    (f : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) ℝ) :
    PeriodicHypercubicEvenBoundaryHaarL2 H N :=
  (memLp_two_of_stronglyMeasurable_uniform_bound
    (periodicHypercubicEvenBoundaryHaarMeasure H N)
    (periodicHypercubicEvenBoundaryProjectedBCFFunction H N hN target f)
    (periodicHypercubicEvenBoundaryProjectedBCFFunction_stronglyMeasurable
      H N hN target f)
    ‖f‖ (norm_nonneg _)
    (periodicHypercubicEvenBoundaryProjectedBCFFunction_abs_le
      H N hN target f)).toLp
    (periodicHypercubicEvenBoundaryProjectedBCFFunction H N hN target f)

/-- The full projected pullback depends only on the shared boundary and is
represented by the projected boundary function. -/
theorem periodicHypercubicEven_singleLinkHeatBathProjection_boundaryBCFPullback
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (target : PeriodicHypercubicEvenEdge H)
    (f : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) ℝ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    let C := periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN 0 (by norm_num)
    C.singleLinkHeatBathProjection target
        (periodicHypercubicEvenBoundaryBCFPullback H N f) A =
      periodicHypercubicEvenBoundaryProjectedBCFFunction
        H N hN target f
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction A) := by
  dsimp only
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN 0 (by norm_num)
  let P := periodicHypercubicEvenEdgeOrbitPartition H
  let O := periodicHypercubicEvenBoundaryBCFPullback H N f
  change C.singleLinkHeatBathProjection target O A =
    periodicHypercubicEvenBoundaryProjectedBCFFunction
      H N hN target f (P.boundaryRestriction A)
  by_cases hTarget : P.side target = ReflectionEdgeSide.fixed
  · rw [continuous_compact_oriented_singleLinkHeatBathProjection_eq_haarIntegral_of_beta_eq_zero
      C (by rfl) target O A]
    unfold periodicHypercubicEvenBoundaryProjectedBCFFunction
    dsimp only
    rw [continuous_compact_oriented_singleLinkHeatBathProjection_eq_haarIntegral_of_beta_eq_zero
      C (by rfl) target O
        (periodicHypercubicEvenCanonicalBoundarySection H N
          (P.boundaryRestriction A))]
    apply integral_congr_ae
    filter_upwards [] with g
    change f (P.boundaryRestriction (C.base.replaceLink A target g)) =
      f (P.boundaryRestriction
        (C.base.replaceLink
          (periodicHypercubicEvenCanonicalBoundarySection H N
            (P.boundaryRestriction A)) target g))
    apply congrArg f
    apply periodicHypercubicEvenBoundaryRestriction_replaceLink_eq_of_eq
      H N hN target hTarget
    simp [P]
  · have hFiber : C.base.OffLinkFiberConstant target O := by
      intro X Y hAgree
      change f (P.boundaryRestriction X) = f (P.boundaryRestriction Y)
      apply congrArg f
      funext e
      have hne : e.1 ≠ target := by
        intro heq
        subst target
        exact hTarget e.2
      exact hAgree e.1 hne
    have hFix :=
      continuous_compact_oriented_singleLinkHeatBathProjection_fixes
        C target O hFiber
    rw [hFix]
    unfold periodicHypercubicEvenBoundaryProjectedBCFFunction
    dsimp only
    rw [hFix]
    simp [O, P, periodicHypercubicEvenBoundaryBCFPullback]

/-- On the dense bounded-continuous boundary core, each beta-zero one-link
projection lands again in the canonical analyzed boundary range. -/
theorem periodicHypercubicEven_singleLinkHeatBathProjectionL2_analysis_toLp_mem_range
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (target : PeriodicHypercubicEvenEdge H)
    (f : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) ℝ) :
    let C := periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN 0 (by norm_num)
    let A := periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
      H N hN 0 (by norm_num)
    C.singleLinkHeatBathProjectionL2 target
        (A (BoundedContinuousFunction.toLp 2
          (periodicHypercubicEvenBoundaryHaarMeasure H N) ℝ f)) =
      A (periodicHypercubicEvenBoundaryProjectedBCFL2 H N hN target f) := by
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN 0 (by norm_num)
  let A := periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
    H N hN 0 (by norm_num)
  let O := periodicHypercubicEvenBoundaryBCFPullback H N f
  let bf := BoundedContinuousFunction.toLp 2
    (periodicHypercubicEvenBoundaryHaarMeasure H N) ℝ f
  let M : ℝ := ‖O‖
  have hM0 : 0 ≤ M := norm_nonneg _
  have hOBound : ∀ X, |O X| ≤ M := by
    intro X
    dsimp [M]
    simpa [Real.norm_eq_abs] using O.norm_coe_le_norm X
  let hOLp := continuous_compact_oriented_memLp_two_of_uniform_bound
    C O O.continuous.stronglyMeasurable M hM0 hOBound
  have hAnalysis : A bf = hOLp.toLp O := by
    apply Lp.ext
    have hA :=
      periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry_coeFn_betaZero
        H N hN bf
    have hbfBoundary :
        bf =ᵐ[periodicHypercubicEvenBoundaryMarginalMeasure
          H N hN 0 (by norm_num)] f := by
      rw [periodicHypercubicEvenBoundaryMarginalMeasure_betaZero H N hN]
      exact BoundedContinuousFunction.coeFn_toLp 2
        (periodicHypercubicEvenBoundaryHaarMeasure H N) ℝ f
    have hbf :=
      (periodicHypercubicEvenSpecialUnitaryBoundaryRestrictionMeasurePreserving
        H N hN 0 (by norm_num)).quasiMeasurePreserving.ae hbfBoundary
    filter_upwards [hA, hbf, hOLp.coeFn_toLp] with X hAX hbX hOX
    calc
      (A bf : _) X = bf ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction X) := hAX
      _ = f ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction X) := hbX
      _ = O X := rfl
      _ = (hOLp.toLp O : _) X := hOX.symm
  let q := periodicHypercubicEvenBoundaryProjectedBCFFunction H N hN target f
  let hqLp := memLp_two_of_stronglyMeasurable_uniform_bound
    (periodicHypercubicEvenBoundaryHaarMeasure H N) q
    (periodicHypercubicEvenBoundaryProjectedBCFFunction_stronglyMeasurable
      H N hN target f)
    ‖f‖ (norm_nonneg _)
    (periodicHypercubicEvenBoundaryProjectedBCFFunction_abs_le
      H N hN target f)
  let hPLp := continuous_compact_oriented_memLp_two_of_uniform_bound
    C (C.singleLinkHeatBathProjection target O)
    (continuous_compact_oriented_singleLinkHeatBathProjection_stronglyMeasurable
      C target O O.continuous.stronglyMeasurable)
    M hM0
    (continuous_compact_oriented_singleLinkHeatBathProjection_abs_le
      C target O O.continuous.stronglyMeasurable M hM0 hOBound)
  have hOutput : hPLp.toLp (C.singleLinkHeatBathProjection target O) =
      A (hqLp.toLp q) := by
    apply Lp.ext
    have hA :=
      periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry_coeFn_betaZero
        H N hN (hqLp.toLp q)
    have hqBoundary :
        hqLp.toLp q =ᵐ[periodicHypercubicEvenBoundaryMarginalMeasure
          H N hN 0 (by norm_num)] q := by
      rw [periodicHypercubicEvenBoundaryMarginalMeasure_betaZero H N hN]
      exact hqLp.coeFn_toLp
    have hq :=
      (periodicHypercubicEvenSpecialUnitaryBoundaryRestrictionMeasurePreserving
        H N hN 0 (by norm_num)).quasiMeasurePreserving.ae hqBoundary
    filter_upwards [hPLp.coeFn_toLp, hA, hq] with X hPX hAX hqX
    calc
      (hPLp.toLp (C.singleLinkHeatBathProjection target O) : _) X =
          C.singleLinkHeatBathProjection target O X := hPX
      _ = q ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction X) :=
        periodicHypercubicEven_singleLinkHeatBathProjection_boundaryBCFPullback
          H N hN target f X
      _ = (hqLp.toLp q : _)
          ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction X) := hqX.symm
      _ = ((hqLp.toLp q : _) ∘
          (periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction) X := rfl
      _ = (A (hqLp.toLp q) : _) X := hAX.symm
  change C.singleLinkHeatBathProjectionL2 target (A bf) =
    A (periodicHypercubicEvenBoundaryProjectedBCFL2 H N hN target f)
  rw [hAnalysis]
  change C.singleLinkHeatBathProjectionL2 target (hOLp.toLp O) =
    A (hqLp.toLp q)
  calc
    C.singleLinkHeatBathProjectionL2 target (hOLp.toLp O) =
        hPLp.toLp (C.singleLinkHeatBathProjection target O) := by
      simpa using
        (continuous_compact_oriented_singleLinkHeatBathProjectionL2_toLp_eq
          C target O O.continuous.stronglyMeasurable M hM0 hOBound)
    _ = A (hqLp.toLp q) := hOutput

/-- Every beta-zero one-link heat-bath projection preserves the complete
canonical analyzed boundary range. -/
theorem periodicHypercubicEven_singleLinkHeatBathProjectionL2_analysis_rangeInvariant_betaZero
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (target : PeriodicHypercubicEvenEdge H)
    (f : PeriodicHypercubicEvenBoundaryHaarL2 H N) :
    ∃ g : PeriodicHypercubicEvenBoundaryHaarL2 H N,
      let C := periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN 0 (by norm_num)
      let A := periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
        H N hN 0 (by norm_num)
      C.singleLinkHeatBathProjectionL2 target (A f) = A g := by
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN 0 (by norm_num)
  let A := periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
    H N hN 0 (by norm_num)
  let S := periodicHypercubicEvenCanonicalBoundarySynthesisL2
    H N hN 0 (by norm_num)
  let Ptarget := C.singleLinkHeatBathProjectionL2 target
  let p : PeriodicHypercubicEvenBoundaryHaarL2 H N → Prop := fun u =>
    A (S (Ptarget (A u))) = Ptarget (A u)
  have hp : p f := by
    apply DenseRange.induction_on (p := p)
      (BoundedContinuousFunction.toLp_denseRange ℝ
        (periodicHypercubicEvenBoundaryHaarMeasure H N) ℝ (by norm_num)) f
    · apply isClosed_eq
      · exact A.continuous.comp
          (S.continuous.comp (Ptarget.continuous.comp A.continuous))
      · exact Ptarget.continuous.comp A.continuous
    · intro O
      have hcore :=
        periodicHypercubicEven_singleLinkHeatBathProjectionL2_analysis_toLp_mem_range
          H N hN target O
      dsimp [p]
      rw [hcore]
      rw [periodicHypercubicEvenCanonicalBoundarySynthesisL2_analysis]
  refine ⟨S (Ptarget (A f)), ?_⟩
  exact hp.symm

/-- Every local beta-zero heat-bath fluctuation preserves the canonical
analyzed boundary range. -/
theorem periodicHypercubicEven_singleLinkHeatBathFluctuationL2_analysis_rangeInvariant_betaZero
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (target : PeriodicHypercubicEvenEdge H)
    (f : PeriodicHypercubicEvenBoundaryHaarL2 H N) :
    ∃ g : PeriodicHypercubicEvenBoundaryHaarL2 H N,
      let C := periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN 0 (by norm_num)
      let A := periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
        H N hN 0 (by norm_num)
      C.singleLinkHeatBathFluctuationL2 target (A f) = A g := by
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN 0 (by norm_num)
  let A := periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
    H N hN 0 (by norm_num)
  rcases
    periodicHypercubicEven_singleLinkHeatBathProjectionL2_analysis_rangeInvariant_betaZero
      H N hN target f with ⟨g, hg⟩
  have hg' : C.singleLinkHeatBathProjectionL2 target (A f) = A g := by
    simpa [C, A] using hg
  refine ⟨f - g, ?_⟩
  dsimp only
  rw [continuous_compact_oriented_singleLinkHeatBathFluctuationL2_apply, hg']
  exact (A.map_sub f g).symm

/-- The actual beta-zero finite Wilson heat-bath Hamiltonian preserves the
canonical boundary-analysis range. -/
theorem periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorRangeInvariant_betaZero
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    realHilbertIsometricAdjointCompressionGeneratorRangeInvariant
      (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
        H N hN 0 (by norm_num))
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN 0 (by norm_num)).heatBathHamiltonianL2 := by
  classical
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN 0 (by norm_num)
  let A := periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
    H N hN 0 (by norm_num)
  intro f
  have hlocal : ∀ target : C.base.geometry.Edge,
      ∃ g : PeriodicHypercubicEvenBoundaryHaarL2 H N,
        C.singleLinkHeatBathFluctuationL2 target (A f) = A g := by
    intro target
    simpa [C, A] using
      (periodicHypercubicEven_singleLinkHeatBathFluctuationL2_analysis_rangeInvariant_betaZero
        H N hN target f)
  choose g hg using hlocal
  refine ⟨∑ target, g target, ?_⟩
  rw [continuous_compact_oriented_heatBathHamiltonianL2_apply]
  calc
    (∑ target : C.base.geometry.Edge,
        C.singleLinkHeatBathFluctuationL2 target (A f)) =
      ∑ target : C.base.geometry.Edge, A (g target) := by
        apply Finset.sum_congr rfl
        intro target _
        exact hg target
    _ = A (∑ target : C.base.geometry.Edge, g target) := by
      simp

/-- The concrete canonical boundary heat-bath generator defect vanishes
unconditionally at beta zero. -/
theorem periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2_betaZero
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2
        H N hN 0 (by norm_num) = 0 := by
  exact
    (realHilbertIsometricAdjointCompressionGeneratorRangeInvariant_iff_defect_eq_zero
      (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
        H N hN 0 (by norm_num))
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN 0 (by norm_num)).heatBathHamiltonianL2).mp
      (periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorRangeInvariant_betaZero
        H N hN)

/-- Consequently, the positive second-moment leakage curvature also vanishes
at beta zero. -/
theorem periodicHypercubicEvenCanonicalBoundaryHeatBathSecondMomentDefectL2_betaZero
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    periodicHypercubicEvenCanonicalBoundaryHeatBathSecondMomentDefectL2
        H N hN 0 (by norm_num) = 0 := by
  exact
    (periodicHypercubicEvenCanonicalBoundaryHeatBathSecondMomentDefectL2_eq_zero_iff_generatorDefect_eq_zero
      H N hN 0 (by norm_num)).2
      (periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2_betaZero
        H N hN)

end

end MathlibAnalytic
end MGAP4D