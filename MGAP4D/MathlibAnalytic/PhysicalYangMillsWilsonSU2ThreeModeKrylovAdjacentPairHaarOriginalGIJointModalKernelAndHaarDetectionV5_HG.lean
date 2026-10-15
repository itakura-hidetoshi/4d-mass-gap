import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGIModalLinearityAnyFineBetaV5_HF
import Mathlib.Tactic

/-!
# P4-Q2-HG: authentic GI joint modal kernel, almost-everywhere detector and Gram witness

HF proved that the true two-interacting-Wilson-posterior expectation
gap is a REAL linear functional on every genuine finite fine-right
Krylov coefficient family, for arbitrary nonnegative fine coupling.

This file constructs the WHOLE physical-link / boundary-context
intersection of those actual GI modal kernels as a real submodule,
retaining its original source-kernel obstruction without assuming
any GI detector injectivity.

Connect the measurable null locus of GL's ORIGINAL signed gap-square
physical detection mass to the *a.e.* family of these genuine kernels,
with frozen beta(n)>0 and arbitrary fine beta(n+1)>=0.

Distinguish a pointwise context witness from positive pair-Haar
measure detection: derive positive Gram from one physical point
ONLY under continuity of the original GI expectation gap in the
boundary context and the genuine pair-Haar full support. This
isolates precisely the analytic continuity requirement without
inventing it, and does not identify the different GU/HB squared
two-left-boundary response with GI's two-posterior expectation gap.

No nonzero zero-depth GI anchor, positive fine-beta source frame,
volume-uniform coercivity, H1-C3 or continuum Yang--Mills gap is
assumed or established.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 2800000
set_option synthInstance.maxHeartbeats 900000

local instance p4Q2HG_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2HG_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2HG_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2HG_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2HG_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

private noncomputable instance p4Q2HG_linksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The TRUE original Wilson spatial pair-Haar probability is positive
on every nonempty open boundary-context set. This holds because every
compact SU(2) coordinate has full-support normalized Haar, and finite
configuration products preserve positive-open support. -/
local instance p4Q2HG_pairHaarOpenPos (H : ℕ) :
    (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2).IsOpenPosMeasure := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint

/-- For a continuous real function against a positive-open measure,
nonvanishing at just ONE point implies nonvanishing on a set of
POSITIVE measure. This makes precise why a single Haar point cannot
be used without an analytic continuity premise. -/
private theorem p4Q2HG_notAEZero_of_continuous_pointWitness
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (μ : Measure X) [μ.IsOpenPosMeasure]
    (F : X → ℝ) (hContinuous : Continuous F)
    (x : X) (hx : F x ≠ 0) :
    ¬ ∀ᵐ y ∂μ, F y = 0 := by
  intro hAE
  have hEq : F = (fun _ : X => (0 : ℝ)) :=
    MeasureTheory.Measure.eq_of_ae_eq hAE hContinuous continuous_const
  exact hx (congrFun hEq x)

section ActualRight

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ)
local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "RightFactor" =>
  physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "Modal" =>
  p4Q2HF_actualRightGIModalLinear
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r

/-- The intersection of ALL true two-Wilson-posterior linear GI
detector kernels at ALL actual physical links and boundary contexts:
a mathematically native real SUBMODULE of the actual finite signed
right Krylov coefficient space for any nonnegative fine coupling. -/
noncomputable def p4Q2HG_actualRightGIJointModalKernel :
    Submodule ℝ (Fin (r + 1) → ℝ) :=
  ⨅ (e : Link), ⨅ (z : Cfg × Cfg), (Modal e z).ker

/-- Membership in the true contextual detector intersection is
precisely pointwise vanishing of every ORIGINAL interacting posterior
GI expectation difference; no alternative posterior or source model. -/
theorem p4Q2HG_actualRightGIJointModalKernel_mem_iff
    (a : Fin (r + 1) → ℝ) :
    a ∈ p4Q2HG_actualRightGIJointModalKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r ↔
    ∀ e : Link, ∀ z : Cfg × Cfg,
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        Hn (beta n) (hbeta n)
        (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) e z = 0 := by
  simp only [p4Q2HG_actualRightGIJointModalKernel,
    Submodule.mem_iInf, LinearMap.mem_ker]
  exact forall₂_congr (fun e z =>
    (p4Q2HF_actualRightGIExpectationGap_eq_modalLinear
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a e z).symm.congr_left)

 /-- Genuine physical source vanishing ALWAYS forces membership in
 the original GI whole-boundary common kernel, with no inverse
 detector-separation assumption and no fine-beta restriction. -/
theorem p4Q2HG_actualSource_zero_mem_GIJointKernel
    (a : Fin (r + 1) → ℝ)
    (hSource :
      (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) = 0) :
    a ∈ p4Q2HG_actualRightGIJointModalKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r := by
  rw [p4Q2HG_actualRightGIJointModalKernel_mem_iff]
  intro e z
  exact p4Q2HD_actualSource_zero_implies_allOriginalGI_null
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r a hSource e z

/-- A true anchor detected at one original Wilson link/context makes
the whole GI kernel a proper finite-dimensional submodule of
codimension at least one. No upper bound on the actual physical
source nullity is invented. -/
theorem p4Q2HG_actualRightGIJointKernel_finrank_le_of_anchor_ne
    (e : Link) (z : Cfg × Cfg)
    (hAnchor :
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        Hn (beta n) (hbeta n) (RightFactor n 0) e z ≠ 0) :
    Module.finrank ℝ
      ↥(p4Q2HG_actualRightGIJointModalKernel
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) ≤ r := by
  have hsub :
      p4Q2HG_actualRightGIJointModalKernel
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
        ≤ (Modal e z).ker := by
    intro a ha
    have hAll :=
      (p4Q2HG_actualRightGIJointModalKernel_mem_iff
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r a).mp ha
    exact (p4Q2HF_actualRightGI_null_iff_mem_modalKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a e z).mp (hAll e z)
  have hDim := p4Q2HF_actualRightGI_modalKernel_finrank_of_anchor_ne
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r e z hAnchor
  exact (Submodule.finrank_mono hsub).trans hDim.le

/-- For genuine FINE beta(n+1)=0, detection of the physical constant
source on at least ONE actual Wilson context gives exact equality
of true GI modal joint kernel with the true physical source kernel. -/
theorem p4Q2HG_fineZero_GIJointKernel_mem_iff_physicalSource_zero
    (hFineZero : beta (n + 1) = 0)
    (hAnchor : ∃ e : Link, ∃ z : Cfg × Cfg,
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        Hn (beta n) (hbeta n) (RightFactor n 0) e z ≠ 0)
    (a : Fin (r + 1) → ℝ) :
    a ∈ p4Q2HG_actualRightGIJointModalKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r ↔
    (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) = 0 := by
  exact (p4Q2HG_actualRightGIJointModalKernel_mem_iff
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r a).trans
    (p4Q2HD_fineZero_allOriginalGI_null_iff_source_zero_of_anchor_exists
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFineZero a hAnchor)

/-- The actual positive-frozen-Wilson GL detection mass of arbitrary
fine-beta signed Krylov sources vanishes exactly when the genuine
finite-dimensional GI linear functional kills those coefficients
pair-Haar ALMOST EVERYWHERE at each real physical spatial link. -/
theorem p4Q2HG_actualRightGLDetectionMass_zero_iff_GIModal_aeKernel
    (hFrozen : 0 < beta n) (a : Fin (r + 1) → ℝ) :
    p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
        Hn (beta n) (hbeta n)
        (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
        (Finset.univ : Finset Link) = 0 ↔
      ∀ e : Link,
        ∀ᵐ z ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure Hn 2,
          a ∈ (Modal e z).ker := by
  rw [p4Q2GM_actualFineRightKrylovDetectionMass_zero_iff_gapAE
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFrozen a]
  constructor
  · intro h e
    filter_upwards [h e] with z hz
    exact (p4Q2HF_actualRightGI_null_iff_mem_modalKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a e z).mp hz
  · intro h e
    filter_upwards [h e] with z hz
    exact (p4Q2HF_actualRightGI_null_iff_mem_modalKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a e z).mpr hz

/-- TRUE Gram nullity implies almost-everywhere annihilation of
the actual finite-dimensional original-Wilson GI modal linear maps
on ALL real physical links. The converse is NOT established. -/
theorem p4Q2HG_actualRightGram_zero_implies_GIModal_aeKernel
    (hFrozen : 0 < beta n) (a : Fin (r + 1) → ℝ)
    (hGram :
      star a ⬝ᵥ (Matrix.mulVec
        (fineRightKrylovPairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) a) = 0) :
      ∀ e : Link,
        ∀ᵐ z ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure Hn 2,
          a ∈ (Modal e z).ker := by
  have hAE :=
    p4Q2GM_actualFineRightKrylovGram_zero_implies_gapAE
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen a hGram
  intro e
  filter_upwards [hAE e] with z hz
  exact (p4Q2HF_actualRightGI_null_iff_mem_modalKernel
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r a e z).mp hz

/-- A SINGLE true nonzero GI expectation-gap value at a physical
pair context proves positive original Wilson Gram Rayleigh, PROVIDED
the same GI gap is continuous in the pair context. Full support of
the genuine spatial pair-Haar measure upgrades the point witness
to a positive-measure witness. Continuity is explicit: no Gaussian
atom or artificial positive-mass singleton is used. -/
theorem p4Q2HG_actualRightGram_pos_of_GI_pointWitness_and_continuous
    (hFrozen : 0 < beta n) (a : Fin (r + 1) → ℝ)
    (e : Link) (z₀ : Cfg × Cfg)
    (hCont : Continuous (fun z : Cfg × Cfg =>
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        Hn (beta n) (hbeta n)
        (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) e z))
    (hPoint :
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        Hn (beta n) (hbeta n)
        (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) e z₀ ≠ 0) :
    0 < star a ⬝ᵥ (Matrix.mulVec
      (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a) := by
  have hNoAE :
      ¬ ∀ᵐ z ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure Hn 2,
        p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          Hn (beta n) (hbeta n)
          (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) e z = 0 :=
    p4Q2HG_notAEZero_of_continuous_pointWitness
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure Hn 2)
      _ hCont z₀ hPoint
  exact p4Q2GM_actualFineRightKrylovGram_pos_of_gapWitness
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFrozen a e hNoAE

end ActualRight
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HG_actualRightGIJointModalKernel_mem_iff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HG_actualSource_zero_mem_GIJointKernel
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HG_actualRightGIJointKernel_finrank_le_of_anchor_ne
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HG_fineZero_GIJointKernel_mem_iff_physicalSource_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HG_actualRightGLDetectionMass_zero_iff_GIModal_aeKernel
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HG_actualRightGram_zero_implies_GIModal_aeKernel
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HG_actualRightGram_pos_of_GI_pointWitness_and_continuous
