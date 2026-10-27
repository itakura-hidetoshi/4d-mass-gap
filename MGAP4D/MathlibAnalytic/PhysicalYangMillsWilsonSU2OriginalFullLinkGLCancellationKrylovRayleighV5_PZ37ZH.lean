import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFullLinkGLPhysicalRayleighV5_PZ37ZG
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonAllFineUnconditionalGLMassV5_OX
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ZH — physical cancellation is the LITERAL original depth-one Krylov source

Preserve the unchanged original SU(2) Wilson normalized one-slab physical
transfer T_t, canonical Gauss-law Hilbert unit U, its true finite right
Krylov source synthesis S_r, the actual TWO INTERACTING Wilson posterior
expectation-gap square over genuine density contrast variance, and the
original FULL-LINK/FULL-boundary Haar GL mass M_GL.

For the literal signed physical coefficients a=(1,-1), not a proxy or
an independent-Haar substitute, prove for all nonnegative fine t

  S_1(a) = U - T_t U = F_t.

The real frozen beta_0=b>0 and the fine beta_1=t remain distinct, and
the physical finite volume H is unchanged. PZ37U/OX then identifies
the exact actual integrated GL zero locus on F_t at ALL t>=0:

  M_GL(H,b;F_t)=0  iff  F_t=0.

Thus every genuinely nonzero such source has strictly positive
GL mass and physical-source Rayleigh M_GL(F_t)/||F_t||².
PZ37ZF makes F_t nonzero for every sufficiently small POSITIVE t,
so the normalized Rayleigh is strictly positive there, while the
PZ37ZG link-count bound remains explicit.

No fine-uniform positive lower numerical constant, ratio limit at
fine zero, arbitrary-volume U0, common physical endpoint E, all-depth
positive fine window F, H1-H4 or continuum mass gap is asserted.
The finite-source limit M_GL(F_t)->0 and coefficient-frame no-go do
NOT by themselves imply a normalized-Rayleigh limit or coercivity
no-go. Never reintroduce the disproved two-context Q_GI/N_H floor.
No Dobrushin, new axiom, sorry, admit or native_decide.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37ZH_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ZH_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ZH_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ZH_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ZH_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2PZ37ZH_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- The REAL fixed signed coefficient vector (1,-1) on zero and
first original physical right-Krylov modes. -/
def p4Q2PZ37ZH_depthOneCancellationCoefficients : Fin (1 + 1) → ℝ :=
  fun j => if j = 0 then 1 else -1

/-- Genuinely frozen/fine scale coupling schedule: beta_0=b and
beta_k=t for all k>0. In particular the depth-one physical orbit
uses fine beta_1=t, while the GL posterior uses frozen beta_0=b. -/
def p4Q2PZ37ZH_adjacentFrozenFineCouplings
    (b : ℝ) (t : Set.Ici (0 : ℝ)) : ℕ → ℝ :=
  fun k => if k = 0 then b else (t : ℝ)

theorem p4Q2PZ37ZH_adjacentFrozenFineCouplings_nonneg
    (b : ℝ) (hb : 0 < b) (t : Set.Ici (0 : ℝ)) :
    ∀ k, 0 ≤ p4Q2PZ37ZH_adjacentFrozenFineCouplings b t k := by
  intro k
  by_cases hk : k = 0
  · simpa [p4Q2PZ37ZH_adjacentFrozenFineCouplings, hk] using hb.le
  · simp [p4Q2PZ37ZH_adjacentFrozenFineCouplings, hk]

/-- Literally in the Gauss-law physical Haar Hilbert space, the
original HJ synthesis on (1,-1) is U-T_fine U. This is true at
every finite physical H and nonnegative fine, not merely as a scalar
GI receiver response or a coefficient Gram statement. -/
theorem p4Q2PZ37ZH_actualDepthOne_signedSource_eq_unit_sub_fine
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ k, 0 ≤ beta k} (n : ℕ) :
    p4Q2HJ_actualRightPhysicalSourceSynthesis
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n 1 p4Q2PZ37ZH_depthOneCancellationCoefficients =
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector
        (halfExtent (n + 1)) 2 -
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
        (beta (n + 1)) (hbeta (n + 1))
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector
          (halfExtent (n + 1)) 2) := by
  let U := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector
    (halfExtent (n + 1)) 2
  let Fine :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
      (beta (n + 1)) (hbeta (n + 1))
  change
    (∑ j : Fin (1 + 1),
      p4Q2PZ37ZH_depthOneCancellationCoefficients j •
        ((Fine ^ (j : ℕ)) U)) = U - Fine U
  simp [p4Q2PZ37ZH_depthOneCancellationCoefficients,
    Fin.sum_univ_two, sub_eq_add_neg]

/-- Exact identification F_t = S_1(1,-1) in the SAME original
physical Hilbert space for every nonnegative fine coupling. -/
theorem p4Q2PZ37ZH_originalPhysicalCancellation_eq_actualDepthOneSynthesis
    (H : ℕ) (b : ℝ) (hb : 0 < b) (t : Set.Ici (0 : ℝ)) :
    p4Q2HJ_actualRightPhysicalSourceSynthesis
      (halfExtent := fun _ => H)
      (beta := p4Q2PZ37ZH_adjacentFrozenFineCouplings b t)
      (hbeta := p4Q2PZ37ZH_adjacentFrozenFineCouplings_nonneg b hb t)
      0 1 p4Q2PZ37ZH_depthOneCancellationCoefficients =
    p4Q2PZ37ZE_originalPhysicalCancellation H t := by
  have hLiteral :=
    p4Q2PZ37ZH_actualDepthOne_signedSource_eq_unit_sub_fine
      (halfExtent := fun _ => H)
      (beta := p4Q2PZ37ZH_adjacentFrozenFineCouplings b t)
      (hbeta := p4Q2PZ37ZH_adjacentFrozenFineCouplings_nonneg b hb t)
      0
  simpa [p4Q2PZ37ZH_adjacentFrozenFineCouplings,
    p4Q2PZ37ZE_originalPhysicalCancellation,
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperatorHalfLine]
    using hLiteral

/-- Actual full-link two-Wilson-posterior Haar GL mass has the EXACT
physical cancellation F_t as its zero locus at ALL nonnegative fine
values. The only witnesses are genuine original spatial link e and
physical boundary left₀; no rank/source-separation assumption. -/
theorem p4Q2PZ37ZH_allFine_originalGLMass_zero_iff_physicalCancellation_zero
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (left₀ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (t : Set.Ici (0 : ℝ)) :
    p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
      H b (le_of_lt hb)
      (p4Q2PZ37ZE_originalPhysicalCancellation H t)
      (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) = 0 ↔
        p4Q2PZ37ZE_originalPhysicalCancellation H t = 0 := by
  let beta := p4Q2PZ37ZH_adjacentFrozenFineCouplings b t
  have hbeta : ∀ k, 0 ≤ beta k :=
    p4Q2PZ37ZH_adjacentFrozenFineCouplings_nonneg b hb t
  have hFrozen : 0 < beta 0 := by
    simpa [beta, p4Q2PZ37ZH_adjacentFrozenFineCouplings] using hb
  have hZero :=
    p4Q2OX_originalPositiveFrozen_allFine_allDepth_massZero_iff_physicalZero
      (halfExtent := fun _ => H) (beta := beta) (hbeta := hbeta)
      0 hFrozen e left₀ 1 p4Q2PZ37ZH_depthOneCancellationCoefficients
  have hS :
      p4Q2HJ_actualRightPhysicalSourceSynthesis
        (halfExtent := fun _ => H) (beta := beta) (hbeta := hbeta)
        0 1 p4Q2PZ37ZH_depthOneCancellationCoefficients =
          p4Q2PZ37ZE_originalPhysicalCancellation H t := by
    exact p4Q2PZ37ZH_originalPhysicalCancellation_eq_actualDepthOneSynthesis
      H b hb t
  rw [hS] at hZero
  simpa [beta, p4Q2PZ37ZH_adjacentFrozenFineCouplings] using hZero

/-- Physical nonzero cancellation implies STRICTLY positive genuine
integrated two-posterior GL mass, at ALL nonnegative fine t for which
F_t != 0. No positive-fine uniform numerical constant is asserted. -/
theorem p4Q2PZ37ZH_originalGLMass_pos_of_physicalCancellation_ne_zero
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (left₀ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (t : Set.Ici (0 : ℝ))
    (hNonzero : p4Q2PZ37ZE_originalPhysicalCancellation H t ≠ 0) :
    0 < p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
      H b (le_of_lt hb)
      (p4Q2PZ37ZE_originalPhysicalCancellation H t)
      (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) := by
  have hNonneg :=
    p4Q2PZ37ZG_originalGL_fullLink_nonneg
      H b hb (p4Q2PZ37ZE_originalPhysicalCancellation H t)
  have hZero :=
    p4Q2PZ37ZH_allFine_originalGLMass_zero_iff_physicalCancellation_zero
      H b hb e left₀ t
  have hMassNe :
      p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
        H b (le_of_lt hb)
        (p4Q2PZ37ZE_originalPhysicalCancellation H t)
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) ≠ 0 := by
    intro hz
    exact hNonzero (hZero.mp hz)
  exact lt_of_le_of_ne hNonneg (Ne.symm hMassNe)

/-- For any genuine nonzero F_t, the exact original Wilson physical
Hilbert-normalized GL Rayleigh is STRICTLY positive, with the already
proved explicit upper cap 2|Links(H)| exp(16b). -/
theorem p4Q2PZ37ZH_originalPhysicalCancellation_Rayleigh_pos_of_ne_zero
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (left₀ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (t : Set.Ici (0 : ℝ))
    (hNonzero : p4Q2PZ37ZE_originalPhysicalCancellation H t ≠ 0) :
    0 < p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh H b hb
      (p4Q2PZ37ZE_originalPhysicalCancellation H t) ∧
    p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh H b hb
      (p4Q2PZ37ZE_originalPhysicalCancellation H t) ≤
      p4Q2PZ37ZG_originalFullLinkGL_RayleighCap H b := by
  have hMassPos :=
    p4Q2PZ37ZH_originalGLMass_pos_of_physicalCancellation_ne_zero
      H b hb e left₀ t hNonzero
  have hNormPos :
      0 < ‖p4Q2PZ37ZE_originalPhysicalCancellation H t‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr hNonzero) 2
  constructor
  · unfold p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh
    exact div_pos hMassPos hNormPos
  · exact (p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh_bounds
      H b hb (p4Q2PZ37ZE_originalPhysicalCancellation H t) hNonzero).2

/-- The physical Rayleigh is ACTUALLY strictly positive throughout
some punctured positive-fine Wilson interval at each finite H,b;
the coefficient-l2 frame no-go near zero remains simultaneously true.
This is qualitative pointwise positivity, not a fine-uniform floor. -/
theorem p4Q2PZ37ZH_originalPositiveFine_cancellation_strictRayleigh
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (left₀ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ t : Set.Ici (0 : ℝ),
        0 < (t : ℝ) → (t : ℝ) < delta →
        0 < p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh H b hb
          (p4Q2PZ37ZE_originalPhysicalCancellation H t) ∧
        p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh H b hb
          (p4Q2PZ37ZE_originalPhysicalCancellation H t) ≤
          p4Q2PZ37ZG_originalFullLinkGL_RayleighCap H b := by
  obtain ⟨delta, hdelta, hNonzero⟩ :=
    p4Q2PZ37ZF_originalPhysicalCancellation_ne_zero_smallPositive H
  refine ⟨delta, hdelta, ?_⟩
  intro t ht hsmall
  exact p4Q2PZ37ZH_originalPhysicalCancellation_Rayleigh_pos_of_ne_zero
    H b hb e left₀ t (hNonzero t ht hsmall)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZH_adjacentFrozenFineCouplings_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZH_actualDepthOne_signedSource_eq_unit_sub_fine
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZH_originalPhysicalCancellation_eq_actualDepthOneSynthesis
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZH_allFine_originalGLMass_zero_iff_physicalCancellation_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZH_originalGLMass_pos_of_physicalCancellation_ne_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZH_originalPhysicalCancellation_Rayleigh_pos_of_ne_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZH_originalPositiveFine_cancellation_strictRayleigh
