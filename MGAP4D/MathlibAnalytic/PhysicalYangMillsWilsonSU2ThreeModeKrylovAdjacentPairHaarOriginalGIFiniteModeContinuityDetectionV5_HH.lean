import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGIJointModalKernelAndHaarDetectionV5_HG
import Mathlib.Tactic

/-!
# P4-Q2-HH: finite genuine GI modal continuity bridges a.e. and all-boundary kernels

HG built the original two-Wilson-posterior GI whole-context linear
detector submodule and connected its a.e.-null locus to the original
GL genuine gap-square detection mass. Its single-point Gram positivity
theorem retained the explicit analytic continuity hypothesis for every
signed source.

HF proves that the ACTUAL two-Wilson-posterior expectation gap of a
signed fine-right Krylov source is a finite linear combination of its
true physical modes, at arbitrary nonnegative fine coupling.

Consequently continuity of the GI detector in the genuine pair boundary
context for each of the r+1 PHYSICAL modes suffices to give continuity
for EVERY signed combination. Together with HG's proved full-support
original pair-Haar, this closes the exact implication:

 original GL detection mass zero iff coefficient is in the
 ALL-BOUNDARY GI linear common kernel,

under only the finite-mode continuity assumption. Nonmembership in
that joint kernel implies strictly positive original GL detection
mass and strictly positive original physical Krylov Gram Rayleigh.
This is a conditional source-separation result; it is NOT a claim
that the required Wilson-posterior finite-mode continuity or joint
kernel equality with the original physical source kernel is already
unconditionally established.

No independent Haar posterior, no positive source-frame hypothesis,
no uniformity in lattice volume/fine depth or continuum Yang--Mills gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 2700000
set_option synthInstance.maxHeartbeats 850000

local instance p4Q2HH_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2HH_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2HH_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2HH_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2HH_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2HH_linksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance p4Q2HH_su2Haar :
    (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)).IsHaarMeasure := by
  dsimp [normalizedCompactHaar]
  infer_instance

local instance p4Q2HH_spatialHaarOpenPos (H : ℕ) :
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).IsOpenPosMeasure := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance p4Q2HH_pairHaarOpenPos (H : ℕ) :
    (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2).IsOpenPosMeasure := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint

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
local notation "GI" =>
  p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
    Hn (beta n) (hbeta n)

/-- For every genuine finite fine-right Krylov family (including
positive fine coupling), continuity of the r+1 original GI
mode detectors on a single physical link implies continuity of
the two-Wilson-posterior GI gap of EVERY signed source on that link.
No continuum or unverified transfer-injectivity claim is involved. -/
theorem p4Q2HH_actualRightGI_gap_continuous_of_finiteModes
    (a : Fin (r + 1) → ℝ) (e : Link)
    (hModes : ∀ j : Fin (r + 1),
      Continuous (fun z : Cfg × Cfg => GI (RightFactor n (j : ℕ)) e z)) :
    Continuous (fun z : Cfg × Cfg =>
      GI (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) e z) := by
  have hFun :
      (fun z : Cfg × Cfg =>
        GI (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) e z) =
      (fun z : Cfg × Cfg =>
        ∑ j : Fin (r + 1), a j * GI (RightFactor n (j : ℕ)) e z) := by
    funext z
    exact p4Q2HF_actualRightOriginalGIExpectationGap_finite_sum
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a e z
  rw [hFun]
  apply continuous_finset_sum
  intro j _hj
  exact continuous_const.mul (hModes j)

/-- Under continuity of ONLY the actual r+1 original Wilson GI mode
receivers, pointwise nullity of the real GI modal map at ALL physical
pair boundaries is equivalent to pair-Haar a.e. nullity at that link.
There is no invented singleton Haar atom. -/
theorem p4Q2HH_actualRightGI_modalPointwise_zero_iff_ae_zero
    (a : Fin (r + 1) → ℝ) (e : Link)
    (hModes : ∀ j : Fin (r + 1),
      Continuous (fun z : Cfg × Cfg => GI (RightFactor n (j : ℕ)) e z)) :
    (∀ z : Cfg × Cfg,
      p4Q2HF_actualRightGIModalLinear
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r e z a = 0) ↔
    (∀ᵐ z ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure Hn 2,
      a ∈ (p4Q2HF_actualRightGIModalLinear
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r e z).ker) := by
  have hContinuous :=
    p4Q2HH_actualRightGI_gap_continuous_of_finiteModes
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a e hModes
  constructor
  · intro hPoint
    filter_upwards with z
    change p4Q2HF_actualRightGIModalLinear
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e z a = 0
    exact hPoint z
  · intro hAE
    have hAEGI :
        ∀ᵐ z ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure Hn 2,
          GI (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) e z = 0 := by
      filter_upwards [hAE] with z hz
      exact (p4Q2HF_actualRightGIExpectationGap_eq_modalLinear
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r a e z).trans ((LinearMap.mem_ker).mp hz)
    have hFun :
        (fun z : Cfg × Cfg =>
          GI (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) e z) =
        (fun _ : Cfg × Cfg => (0 : ℝ)) :=
      MeasureTheory.Measure.eq_of_ae_eq hAEGI hContinuous continuous_const
    intro z
    exact (p4Q2HF_actualRightGIExpectationGap_eq_modalLinear
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a e z).symm.trans (congrFun hFun z)

/-- Once the FINITE set of genuine GI Krylov modal receivers is
continuous on the pair boundary at each actual link, GL's measured
source detection null locus equals precisely the whole-context
original GI common real linear kernel, for arbitrary fine beta. -/
theorem p4Q2HH_actualRightGLMass_zero_iff_GI_jointKernel_of_modeContinuity
    (hFrozen : 0 < beta n)
    (hModes : ∀ e : Link, ∀ j : Fin (r + 1),
      Continuous (fun z : Cfg × Cfg => GI (RightFactor n (j : ℕ)) e z))
    (a : Fin (r + 1) → ℝ) :
    p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
        Hn (beta n) (hbeta n)
        (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
        (Finset.univ : Finset Link) = 0 ↔
      a ∈ p4Q2HG_actualRightGIJointModalKernel
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r := by
  rw [p4Q2HG_actualRightGLDetectionMass_zero_iff_GIModal_aeKernel
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFrozen a]
  constructor
  · intro hAE
    apply (p4Q2HG_actualRightGIJointModalKernel_mem_iff
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a).mpr
    intro e z
    have hAll :=
      (p4Q2HH_actualRightGI_modalPointwise_zero_iff_ae_zero
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r a e (hModes e)).mpr (hAE e)
    exact (p4Q2HF_actualRightGIExpectationGap_eq_modalLinear
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a e z).trans (hAll z)
  · intro hJoint e
    have hAll :=
      (p4Q2HG_actualRightGIJointModalKernel_mem_iff
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r a).mp hJoint
    have hPoint (z : Cfg × Cfg) :
        p4Q2HF_actualRightGIModalLinear
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r e z a = 0 :=
      (p4Q2HF_actualRightGIExpectationGap_eq_modalLinear
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r a e z).symm.trans (hAll e z)
    exact (p4Q2HH_actualRightGI_modalPointwise_zero_iff_ae_zero
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a e (hModes e)).mp hPoint

/-- If an actual finite signed physical Krylov coefficient vector
falls OUTSIDE the real whole-boundary GI kernel, then the original
GL two-interacting-Wilson-posterior gap-square mass is STRICTLY
positive once the r+1 actual GI mode receivers are continuous.
The coefficient vector need not be independent in the physical space. -/
theorem p4Q2HH_actualRightGLMass_pos_of_not_mem_jointKernel
    (hFrozen : 0 < beta n)
    (hModes : ∀ e : Link, ∀ j : Fin (r + 1),
      Continuous (fun z : Cfg × Cfg => GI (RightFactor n (j : ℕ)) e z))
    (a : Fin (r + 1) → ℝ)
    (hNot : a ∉ p4Q2HG_actualRightGIJointModalKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r) :
    0 < p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
      Hn (beta n) (hbeta n)
      (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
      (Finset.univ : Finset Link) := by
  have hNonneg :=
    p4Q2GM_originalWilsonGapSquarePatch_nonneg
      Hn (beta n) hFrozen
      (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
      (Finset.univ : Finset Link)
  have hNe :
      p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
        Hn (beta n) (hbeta n)
        (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
        (Finset.univ : Finset Link) ≠ 0 := by
    intro hZero
    exact hNot ((p4Q2HH_actualRightGLMass_zero_iff_GI_jointKernel_of_modeContinuity
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen hModes a).mp hZero)
  exact lt_of_le_of_ne hNonneg (Ne.symm hNe)

/-- Under continuity of the finite set of genuine GI physical
Krylov mode detectors, every coefficient vector NOT lying in the
joint physical GI kernel has STRICTLY positive original physical
Krylov Gram Rayleigh. The true analytic mode-continuity premise
remains explicitly stated and no uniform quantitative gap is claimed. -/
theorem p4Q2HH_actualRightGram_pos_of_not_mem_jointKernel
    (hFrozen : 0 < beta n)
    (hModes : ∀ e : Link, ∀ j : Fin (r + 1),
      Continuous (fun z : Cfg × Cfg => GI (RightFactor n (j : ℕ)) e z))
    (a : Fin (r + 1) → ℝ)
    (hNot : a ∉ p4Q2HG_actualRightGIJointModalKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r) :
    0 < star a ⬝ᵥ (Matrix.mulVec
      (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a) := by
  have hWitness :
      ∃ e : Link, ∃ z : Cfg × Cfg,
        GI (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) e z ≠ 0 := by
    by_contra hNone
    push_neg at hNone
    exact hNot ((p4Q2HG_actualRightGIJointModalKernel_mem_iff
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a).mpr hNone)
  obtain ⟨e, z, hWitness⟩ := hWitness
  exact p4Q2HG_actualRightGram_pos_of_GI_pointWitness_and_continuous
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFrozen a e z
    (p4Q2HH_actualRightGI_gap_continuous_of_finiteModes
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a e (hModes e))
    hWitness

end ActualRight
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HH_actualRightGI_gap_continuous_of_finiteModes
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HH_actualRightGI_modalPointwise_zero_iff_ae_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HH_actualRightGLMass_zero_iff_GI_jointKernel_of_modeContinuity
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HH_actualRightGLMass_pos_of_not_mem_jointKernel
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HH_actualRightGram_pos_of_not_mem_jointKernel
