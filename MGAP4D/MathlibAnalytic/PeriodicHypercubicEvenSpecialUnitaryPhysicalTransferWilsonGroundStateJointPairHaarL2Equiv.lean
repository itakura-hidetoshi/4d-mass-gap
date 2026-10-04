import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointPairHaarL2Isometry
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/-!
# Exact pair-Haar / ground-state joint L² equivalence

The preceding half-density isometry sends a pair-Haar representative `f` to

  f / sqrt(w)

in the genuine ground-state joint law `dπ = w dμ`.

Because the normalized density is strictly positive pair-Haar almost
everywhere and pair Haar is absolutely continuous with respect to the joint
law, the inverse representative is

  g ↦ sqrt(w) * g.

This file constructs that inverse on `L²`, proves both pointwise-a.e.
cancellations on the correct measures, and upgrades the existing linear
isometry to a genuine real `LinearIsometryEquiv`.

This is only a Hilbert-space change of measure.  It does not identify any
conditional expectation with the physical transfer operator and does not
reintroduce H1-D5 exact descent.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Filter
open scoped InnerProductSpace InnerProduct ENNReal

noncomputable section

local instance groundStateJointPairHaarL2EquivTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance groundStateJointPairHaarL2EquivCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance groundStateJointPairHaarL2EquivSecondCountable
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance groundStateJointPairHaarL2EquivMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance groundStateJointPairHaarL2EquivBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance groundStateJointPairHaarL2EquivSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Representative-level square-root-density transform from the genuine
ground-state joint law back to pair Haar. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointToPairHaarFunction
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta))
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSqrtDensity
      H N hN beta hbeta z *
    g z

/-- The square-root-density representative belongs to pair-Haar `L²`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointToPairHaarFunction_memLp
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta)) :
    MemLp
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointToPairHaarFunction
        H N hN beta hbeta g)
      2
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  let μ :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
  let ν :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
      H N hN beta hbeta
  let w :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
      H N hN beta hbeta
  let sqrtw := fun z =>
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSqrtDensity
      H N hN beta hbeta z
  let v := fun z => sqrtw z * g z
  let rho := fun z => ENNReal.ofReal (w z)
  have hwStrong : AEStronglyMeasurable w μ :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight_integrable
      H N hN beta hbeta).aestronglyMeasurable
  have hsqrtStrong : AEStronglyMeasurable sqrtw μ := by
    dsimp [sqrtw,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSqrtDensity]
    exact Real.continuous_sqrt.comp_aestronglyMeasurable hwStrong
  have hμν : μ ≪ ν := by
    simpa [μ, ν] using
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure_absolutelyContinuous_groundStateJointMeasure
        H N hN beta hbeta
  have hgStrongμ : AEStronglyMeasurable (fun z => g z) μ :=
    (Lp.aestronglyMeasurable g).mono_ac hμν
  have hvStrongμ : AEStronglyMeasurable v μ := by
    exact hsqrtStrong.mul hgStrongμ
  have hrhoAE : AEMeasurable rho μ := by
    exact hwStrong.aemeasurable.ennreal_ofReal
  have hrhoTop : ∀ᵐ z ∂μ, rho z < (⊤ : ENNReal) := by
    filter_upwards with z
    simp [rho]
  have hgSqIntν : Integrable (fun z => g z ^ 2) (μ.withDensity rho) := by
    have hgSqInt : Integrable (fun z => g z ^ 2) ν :=
      (Lp.memLp g).integrable_sq
    simpa [ν, μ, rho, w,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure] using hgSqInt
  have hWeighted :
      Integrable (fun z => (rho z).toReal • (g z ^ 2)) μ := by
    exact
      (integrable_withDensity_iff_integrable_smul₀' hrhoAE hrhoTop).1 hgSqIntν
  have hwpos :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight_ae_pos
      H N hN beta hbeta
  have hvSqInt : Integrable (fun z => v z ^ 2) μ := by
    apply hWeighted.congr
    filter_upwards [hwpos] with z hz
    have hsqrt_sq :
        sqrtw z ^ 2 =
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
            H N hN beta hbeta z := by
      dsimp [sqrtw,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSqrtDensity]
      exact Real.sq_sqrt hz.le
    simp only [smul_eq_mul]
    dsimp [rho, v]
    rw [ENNReal.toReal_ofReal hz.le]
    rw [← hsqrt_sq]
    ring
  have hvMem : MemLp v 2 μ :=
    (memLp_two_iff_integrable_sq hvStrongμ).2 hvSqInt
  simpa [v, sqrtw, μ,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointToPairHaarFunction] using hvMem

/-- Square-root-density transport as an actual pair-Haar `L²` vector. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointToPairHaarL2
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta)) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointToPairHaarFunction_memLp
    H N hN beta hbeta g).toLp
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointToPairHaarFunction
      H N hN beta hbeta g)

/-- The pair-Haar `L²` inverse transport has the expected representative. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointToPairHaarL2_coeFn
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointToPairHaarL2
        H N hN beta hbeta g =ᵐ[
          periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N]
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointToPairHaarFunction
        H N hN beta hbeta g :=
  MemLp.coeFn_toLp
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointToPairHaarFunction_memLp
      H N hN beta hbeta g)

/-- Pair-Haar-to-joint transport after square-root-density inverse transport is
the identity on genuine ground-state joint `L²`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2_jointToPairHaar
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointToPairHaarL2
          H N hN beta hbeta g) =
      g := by
  let μ :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
  let ν :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
      H N hN beta hbeta
  have hνμ : ν ≪ μ := by
    simpa [ν, μ] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_absolutelyContinuous_pairHaar
        H N hN beta hbeta
  have hVμ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointToPairHaarL2_coeFn
      H N hN beta hbeta g
  have hVν :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointToPairHaarL2
          H N hN beta hbeta g =ᵐ[ν]
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointToPairHaarFunction
          H N hN beta hbeta g :=
    hνμ.ae_eq hVμ
  have hsqrtPosμ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSqrtDensity_ae_pos
      H N hN beta hbeta
  have hsqrtPosν :
      ∀ᵐ z ∂ν,
        0 <
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSqrtDensity
            H N hN beta hbeta z :=
    hsqrtPosμ.filter_mono
      (Measure.ae_le_iff_absolutelyContinuous.mpr hνμ)
  apply Lp.ext
  filter_upwards
    [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2_coeFn
      H N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointToPairHaarL2
        H N hN beta hbeta g),
      hVν,
      hsqrtPosν] with z hU hV hpos
  rw [hU]
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointFunction
  rw [hV]
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointToPairHaarFunction
  field_simp [ne_of_gt hpos]

/-- Square-root-density inverse transport after pair-Haar-to-joint transport is
the identity on pair-Haar `L²`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointToPairHaarL2_pairHaarToJoint
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointToPairHaarL2
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2
          H N hN beta hbeta f) =
      f := by
  let μ :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
  let ν :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
      H N hN beta hbeta
  have hμν : μ ≪ ν := by
    simpa [μ, ν] using
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure_absolutelyContinuous_groundStateJointMeasure
        H N hN beta hbeta
  have hUν :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2_coeFn
      H N hN beta hbeta f
  have hUμ :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2
          H N hN beta hbeta f =ᵐ[μ]
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointFunction
          H N hN beta hbeta f :=
    hμν.ae_eq hUν
  have hsqrtPosμ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSqrtDensity_ae_pos
      H N hN beta hbeta
  apply Lp.ext
  filter_upwards
    [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointToPairHaarL2_coeFn
      H N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2
        H N hN beta hbeta f),
      hUμ,
      hsqrtPosμ] with z hV hU hpos
  rw [hV]
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointToPairHaarFunction
  rw [hU]
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointFunction
  field_simp [ne_of_gt hpos]

/-- The pair-Haar-to-joint half-density linear isometry is surjective. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2LinearIsometry_surjective
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Function.Surjective
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2LinearIsometry
        H N hN beta hbeta) := by
  intro g
  refine
    ⟨periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointToPairHaarL2
      H N hN beta hbeta g, ?_⟩
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2_jointToPairHaar
      H N hN beta hbeta g

/-- The exact half-density change of measure is a real-linear isometric
equivalence between ordered pair-Haar `L²` and the genuine ground-state joint
`L²` carrier. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N ≃ₗᵢ[ℝ]
      Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta) :=
  LinearIsometryEquiv.ofSurjective
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2LinearIsometry
      H N hN beta hbeta)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2LinearIsometry_surjective
      H N hN beta hbeta)

/-- The equivalence agrees pointwise with the already-constructed forward
half-density isometry. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv_apply
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
        H N hN beta hbeta f =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2
        H N hN beta hbeta f := by
  rfl

/-- The inverse of the equivalence is exactly multiplication by `sqrt(w)`. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv_symm_apply
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta)) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
        H N hN beta hbeta).symm g =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointToPairHaarL2
        H N hN beta hbeta g := by
  apply
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2LinearIsometry
      H N hN beta hbeta).injective
  calc
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2LinearIsometry
        H N hN beta hbeta
        ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
          H N hN beta hbeta).symm g) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
        H N hN beta hbeta
        ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
          H N hN beta hbeta).symm g) := by
      rfl
    _ = g := LinearIsometryEquiv.apply_symm_apply _ g
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2LinearIsometry
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointToPairHaarL2
          H N hN beta hbeta g) := by
      exact
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2_jointToPairHaar
          H N hN beta hbeta g).symm

end

end MathlibAnalytic
end MGAP4D
