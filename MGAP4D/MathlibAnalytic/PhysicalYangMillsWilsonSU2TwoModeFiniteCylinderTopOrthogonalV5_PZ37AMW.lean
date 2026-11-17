import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalNormalizedOneSlabNonidentityV5_PZ37AMV
import MGAP4D.MathlibAnalytic.SpecialUnitaryTwoWilsonEnergyContinuousGramSchmidtClassFunction
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AMW — physical top-orthogonal excitation from TWO native Wilson modes

AMU's abstract Hilbert-basis extension proves a unit physical excitation,
but by itself gives no finite Wilson-cylinder representative. This unit
constructs a nonzero physical top-eigenspace-orthogonal vector **in the
two-dimensional span of the first two actual Wilson energy Gram–Schmidt
plaquette modes**. It is a specific two-term finite cylinder polynomial
in the existing true time-zero spatial plaquette Wilson energy.

This is a finite-volume physical gauge-invariant Hilbert statement, not
a positive-time OS observable or a Wilson–OS one-slab identification.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

local instance p4Q2PZ37AMW_spatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- An explicit TWO-mode linear combination in any real inner-product space
that is nonzero and orthogonal to a prescribed vector. No dimension,
surjectivity, or orthogonal-complement existence assumption is used. -/
private theorem p4Q2PZ37AMW_twoMode_linearCombination
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Ω v0 v1 : E)
    (hv0 : ‖v0‖ = 1)
    (hv1 : ‖v1‖ = 1)
    (h10 : inner ℝ v1 v0 = 0) :
    ∃ c0 c1 : ℝ,
      c0 • v0 + c1 • v1 ≠ 0 ∧
      inner ℝ Ω (c0 • v0 + c1 • v1) = 0 := by
  let a : ℝ := inner ℝ Ω v0
  let b : ℝ := inner ℝ Ω v1
  by_cases ha : a = 0
  · have hv0ne : v0 ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hv0
      norm_num at hv0
    refine ⟨1, 0, ?_, ?_⟩
    · simpa using hv0ne
    · simpa [a] using ha
  · have hself : inner ℝ v1 v1 = 1 := by
      rw [real_inner_self_eq_norm_sq, hv1]
      norm_num
    have hval : inner ℝ v1 (b • v0 + (-a) • v1) = -a := by
      rw [inner_add_right, real_inner_smul_right,
        real_inner_smul_right, h10, hself]
      ring
    have hwne : b • v0 + (-a) • v1 ≠ 0 := by
      intro hw
      rw [hw, inner_zero] at hval
      exact ha (by linarith)
    have horth : inner ℝ Ω (b • v0 + (-a) • v1) = 0 := by
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
      dsimp [a, b]
      ring
    exact ⟨b, -a, hwne, horth⟩

/-- A concrete nonzero true SU(2) Wilson physical Gauss-law excitation, with
only the first two original spatial plaquette Gram–Schmidt modes as input.

The coefficients are REAL scalars determined by the canonical original
normalized Wilson top eigenvector, not an assumed OS boundary state.
The one-dimensional full-top theorem is already proved on this same
finite-volume Wilson model and not supplied as an extra hypothesis. -/
theorem p4Q2PZ37AMW_exists_twoMode_nonzero_originalPhysicalTopOrthogonal
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ∃ c0 c1 : ℝ,
      (c0 • p4Q2PZ37AMU_actualPhysicalGaussMode H 0 +
        c1 • p4Q2PZ37AMU_actualPhysicalGaussMode H 1) ≠ 0 ∧
      (c0 • p4Q2PZ37AMU_actualPhysicalGaussMode H 0 +
        c1 • p4Q2PZ37AMU_actualPhysicalGaussMode H 1) ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
          H 2 (by norm_num) beta hbeta := by
  have hTwo : 0 < (2 : ℕ) := by norm_num
  let Ω : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
      H 2 hTwo beta hbeta
  let v0 : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2 :=
    p4Q2PZ37AMU_actualPhysicalGaussMode H 0
  let v1 : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2 :=
    p4Q2PZ37AMU_actualPhysicalGaussMode H 1
  have ho := p4Q2PZ37AMU_actualPhysicalGaussMode_orthonormal H
  have hv0 : ‖v0‖ = 1 := by
    simpa [v0] using ho.1 0
  have hv1 : ‖v1‖ = 1 := by
    simpa [v1] using ho.1 1
  have h10 : inner ℝ v1 v0 = 0 := by
    simpa [v1, v0] using ho.inner_eq_zero (by decide : (1 : ℕ) ≠ 0)
  obtain ⟨c0, c1, hne, horth⟩ :=
    p4Q2PZ37AMW_twoMode_linearCombination Ω v0 v1 hv0 hv1 h10
  have htop :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
          H 2 hTwo beta hbeta = ℝ ∙ Ω := by
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_eq_span_nonnegativeTopEigenvector
        H 2 hTwo beta hbeta
  have hmem :
      c0 • v0 + c1 • v1 ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
          H 2 hTwo beta hbeta := by
    change c0 • v0 + c1 • v1 ∈
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
        H 2 hTwo beta hbeta)ᗮ
    rw [htop]
    exact (Submodule.mem_orthogonal_singleton_iff_inner_right
      (𝕜 := ℝ) (u := Ω) (v := c0 • v0 + c1 • v1)).mpr horth
  refine ⟨c0, c1, ?_, ?_⟩
  · simpa only [v0, v1] using hne
  · simpa only [v0, v1] using hmem

/-- The two mode coefficients determine an ACTUAL Haar-a.e. Wilson-cylinder
observable, not just an existential vector in abstract physical Hilbert space.
All L² functions and the right-hand side live on the same native physical
time-zero SU(2) configuration carrier. -/
theorem p4Q2PZ37AMW_twoMode_ae_originalSpatialWilsonObservable
    (H : ℕ) (c0 c1 : ℝ) :
    ((c0 • p4Q2PZ37AMU_actualPhysicalGaussMode H 0 +
        c1 • p4Q2PZ37AMU_actualPhysicalGaussMode H 1 :
          PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2) :
      Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2))
      =ᵐ[periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2]
      (fun A =>
        c0 * specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 0
            (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A) +
        c1 * specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 1
            (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A)) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let v0 : Lp ℝ 2 μ := p4Q2PZ37AMU_actualPhysicalGaussMode H 0
  let v1 : Lp ℝ 2 μ := p4Q2PZ37AMU_actualPhysicalGaussMode H 1
  have h0 :
      v0 =ᵐ[μ]
        (fun A => specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 0
          (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A)) := by
    simpa [v0, p4Q2PZ37AMU_actualPhysicalGaussMode] using
      p4Q2PZ37AMT_spatialMode_coeFn H 0
  have h1 :
      v1 =ᵐ[μ]
        (fun A => specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 1
          (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A)) := by
    simpa [v1, p4Q2PZ37AMU_actualPhysicalGaussMode] using
      p4Q2PZ37AMT_spatialMode_coeFn H 1
  have hadd := Lp.coeFn_add (c0 • v0) (c1 • v1)
  have hs0 := Lp.coeFn_smul c0 v0
  have hs1 := Lp.coeFn_smul c1 v1
  change (c0 • v0 + c1 • v1)
      =ᵐ[μ]
      (fun A =>
        c0 * specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 0
            (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A) +
        c1 * specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 1
            (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A))
  filter_upwards [hadd, hs0, hs1, h0, h1] with A ha hs0a hs1a h0a h1a
  rw [ha, hs0a, hs1a, h0a, h1a]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AMW_twoMode_linearCombination
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AMW_exists_twoMode_nonzero_originalPhysicalTopOrthogonal
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AMW_twoMode_ae_originalSpatialWilsonObservable
