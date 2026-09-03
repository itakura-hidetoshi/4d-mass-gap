import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryFinitePhysicalTransferMarkovStep
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open MeasureTheory
open scoped InnerProductSpace InnerProduct

local instance finitePhysicalTransferProjectedTailTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance finitePhysicalTransferProjectedTailCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance finitePhysicalTransferProjectedTailSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance finitePhysicalTransferProjectedTailMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance finitePhysicalTransferProjectedTailBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance finitePhysicalTransferProjectedTailSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- With the right spatial boundary fixed, the temporal crossing kernel is
continuous in the left boundary.  This direct finite-link induction avoids
routing the section through the full product-space continuity theorem. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel_right_continuous
    (H N : ℕ)
    (beta : ℝ)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    Continuous
      (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel H N beta A B) := by
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
  generalize periodicHypercubicEvenSpatialSliceLinkList H = es
  induction es with
  | nil =>
      simpa using
        (continuous_const : Continuous
          (fun _ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
            (1 : ℝ)))
  | cons e es ih =>
      simp only [List.map_cons, List.prod_cons]
      have hleft : Continuous
          (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N => A e) :=
        continuous_apply e
      have hlocal : Continuous
          (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
            specialUnitaryWilsonRelativeKernel N beta (A e) (B e)) :=
        (continuous_specialUnitaryWilsonRelativeKernel N beta).comp₂ hleft continuous_const
      exact hlocal.mul ih

/-- With the right boundary fixed, the complete one-slab Wilson kernel is
continuous in the left boundary. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_right_continuous
    (H N : ℕ)
    (beta : ℝ)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    Continuous
      (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A B) := by
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
  have hw := periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight_continuous H N beta
  have hcross :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel_right_continuous
      H N beta B
  exact (hw.mul hcross).mul continuous_const

/-- For a fixed right boundary `B`, the literal adjacent Wilson one-slab kernel
`A ↦ K(A,B)` is an ambient spatial-slice Haar `L²` vector.  The proof uses only
the fixed-boundary continuity and the canonical pointwise bound `|K| ≤ 1` on
Haar probability space. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_right_memLp_two
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    MemLp
      (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A B)
      2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  refine MemLp.of_bound
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_right_continuous
      H N beta B).aestronglyMeasurable 1 ?_
  exact Filter.Eventually.of_forall fun A => by
    simpa [Real.norm_eq_abs] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
        H N hN beta hbeta A B

/-- Ambient Haar-`L²` realization of the right one-slab kernel section
`A ↦ K(A,B)`. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelRightL2
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) :=
  (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_right_memLp_two
    H N hN beta hbeta B).toLp
      (fun A => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A B)

/-- The ambient `L²` right kernel section has the literal Wilson-kernel
representative almost everywhere. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelRightL2_coeFn
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    (fun A =>
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelRightL2
        H N hN beta hbeta B A) =ᵐ[
          periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N]
      (fun A => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A B) :=
  (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_right_memLp_two
    H N hN beta hbeta B).coeFn_toLp

/-- Canonical packaging of an arbitrary ambient spatial-slice Haar `L²` vector
as a physical Gauss-law vector by orthogonal projection. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryGaussLawProjectedPhysicalVector
    (H N : ℕ)
    (g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N :=
  ⟨periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N g,
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection_mem H N g⟩

@[simp] theorem periodicHypercubicEvenSpecialUnitaryGaussLawProjectedPhysicalVector_coe
    (H N : ℕ)
    (g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    ((periodicHypercubicEvenSpecialUnitaryGaussLawProjectedPhysicalVector H N g :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
      Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) =
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N g := by
  rfl

/-- A physical first argument sees only the Gauss-law projection of an arbitrary
ambient second argument.  Equivalently, the orthogonal complement removed by
Gauss-law projection is invisible to the physical one-slab matrix coefficient. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_inner_projected_eq_ambient
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta f)
        (periodicHypercubicEvenSpecialUnitaryGaussLawProjectedPhysicalVector H N g) =
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta
          (f : Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))) g := by
  let K := periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N
  let P := periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N
  let x :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
      H N hN beta hbeta
      (f : Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
  have hx : x ∈ K :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_preserves_GaussLaw
      H N hN beta hbeta f.property
  have hrem : g - P g ∈ Kᗮ := by
    simpa [K, P] using
      periodicHypercubicEvenSpecialUnitarySpatialSlice_sub_GaussLawProjection_mem_orthogonal H N g
  have horth : inner ℝ x (g - P g) = 0 :=
    (Submodule.mem_orthogonal K (g - P g)).1 hrem x hx
  change inner ℝ x (P g) = inner ℝ x g
  rw [inner_sub_right] at horth
  linarith

/-- Raw-integral form of the previous projection bridge.  The right test vector
may be arbitrary ambient Haar `L²`; the physical coefficient uses its canonical
Gauss-law projection, while the literal Wilson integral still uses the original
ambient representative. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_inner_projected_eq_rawIntegral
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta f)
        (periodicHypercubicEvenSpecialUnitaryGaussLawProjectedPhysicalVector H N g) =
      ∫ p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta p.1 p.2 *
          ((f : Lp ℝ 2
              (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) p.1 * g p.2)
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_inner_projected_eq_ambient]
  exact
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_inner_eq_rawIntegral
      H N hN beta hbeta
      (f : Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) g

/-- The first two literal adjacent Wilson slabs can therefore be packaged as an
actual physical one-slab transfer coefficient against the Gauss-law projection
of the second-slab kernel section. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_inner_projectedKernelRight_eq_rawTwoSlab
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta f)
        (periodicHypercubicEvenSpecialUnitaryGaussLawProjectedPhysicalVector H N
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelRightL2
            H N hN beta hbeta B)) =
      ∫ p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta p.1 p.2 *
          ((f : Lp ℝ 2
              (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) p.1 *
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta p.2 B)
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_inner_projected_eq_rawIntegral]
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  have hsection :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelRightL2_coeFn
      H N hN beta hbeta B
  have hsectionPair :
      (fun p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelRightL2
          H N hN beta hbeta B p.2) =ᵐ[μ.prod μ]
      (fun p => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta p.2 B) := by
    simpa [μ] using
      (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae_eq hsection
  apply integral_congr_ae
  simpa [periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure, μ] using
    hsectionPair.mono fun p hp => by
      have hp' :
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelRightL2
              H N hN beta hbeta B p.2 =
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
              H N beta p.2 B := by
        simpa using hp
      change
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta p.1 p.2 *
            ((f : Lp ℝ 2
              (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) p.1 *
              periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelRightL2
                H N hN beta hbeta B p.2) =
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta p.1 p.2 *
            ((f : Lp ℝ 2
              (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) p.1 *
              periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                H N beta p.2 B)
      rw [hp']

end

end MathlibAnalytic
end MGAP4D
