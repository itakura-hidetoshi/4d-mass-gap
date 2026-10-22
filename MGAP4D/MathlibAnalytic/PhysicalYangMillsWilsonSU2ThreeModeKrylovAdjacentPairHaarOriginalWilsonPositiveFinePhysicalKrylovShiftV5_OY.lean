import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonAllDepthGIKernelFaithfulnessV5_OW
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabTransferRawIntegral
import Mathlib.Tactic

/-!
# P4-Q2-OY — strictly positive original Wilson physical energy and Krylov shift faithfulness

LJ proved that the ACTUAL complete finite-volume positive-coupling SU(2)
Wilson one-slab Haar kernel (including BOTH original spatial
half-Boltzmann weights) has STRICTLY POSITIVE double Haar quadratic
energy for every nonzero continuous signed spatial source.

This module transports that strict original kernel energy to the
GIVEN real Gauss-law physical one-slab transfer, using its exact
physical Hilbert matrix coefficient and genuine product Haar (not a
substitute conditional posterior). Thus every NONZERO physical source
possessing a continuous representative satisfies

  <T_raw(t) f, f> > 0   for ALL positive t,

and so the actual unnormalized/normalized physical Wilson transfer
cannot annihilate such a source. Crucially, OW has already proved
continuous Gauss-law representatives for ALL actual finite Krylov
sources S_r(a), with arbitrary nonnegative fine coupling.

Consequently at every true finite H, every positive fine t and every
finite r, the ORIGINAL Wilson transfer is strictly positive on every
nonzero actual Krylov physical source, and the physical source
coefficient kernel is preserved by shifting its entire right-Krylov
orbit one step:

  S_r(a)=0  <->  Σ_j a_j T_t^(j+1) U = 0.

This is an unconditional non-annihilation / no-nilpotent physical
analytic result. It does NOT assert all three modes U,TU,T²U are
independent, a third-order Gram determinant, a volume-uniform
coercivity floor, or a continuum Yang--Mills mass gap.

No independent-Haar posterior, surrogate Wilson kernel, Dobrushin,
sorry, admit or new axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2OY_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2OY_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2OY_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2OY_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2OY_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

section OriginalWilsonTruePhysicalPositiveEnergy
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "K" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2
local notation "Raw" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive

/-- The literal physical inner product equals the original complete
Wilson spatial-pair Haar integral of the SAME continuous representative.
The only transport is the canonical Haar-L² a.e. identity, lifted along
actual probability-measure-preserving first/second projections. -/
theorem p4Q2OY_originalPhysicalWilson_inner_eq_originalContinuousHaarDouble
    (t : ℝ) (ht : 0 ≤ t) (f : Phys) (psi : C(Cfg, ℝ))
    (hRep : (fun A : Cfg => ((f : Phys) : Lp ℝ 2 haar) A) =ᵐ[haar] psi) :
    inner ℝ (Raw t ht f) f =
      ∫ p : Cfg × Cfg,
        K t p.1 p.2 * (psi p.1 * psi p.2) ∂(Measure.prod haar haar) := by
  have hRaw :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_inner_eq_rawIntegral
      H 2 specialUnitaryTwoWilsonRankPositive t ht f f
  have hFirst :
      (fun p : Cfg × Cfg => ((f : Phys) : Lp ℝ 2 haar) p.1)
        =ᵐ[Measure.prod haar haar] (fun p => psi p.1) := by
    simpa only [Function.comp_def] using
      ((measurePreserving_fst (μ := haar) (ν := haar)).quasiMeasurePreserving.ae_eq hRep)
  have hSecond :
      (fun p : Cfg × Cfg => ((f : Phys) : Lp ℝ 2 haar) p.2)
        =ᵐ[Measure.prod haar haar] (fun p => psi p.2) := by
    simpa only [Function.comp_def] using
      ((measurePreserving_snd (μ := haar) (ν := haar)).quasiMeasurePreserving.ae_eq hRep)
  calc
    inner ℝ (Raw t ht f) f =
        ∫ p : Cfg × Cfg,
          K t p.1 p.2 *
            (((f : Phys) : Lp ℝ 2 haar) p.1 *
              ((f : Phys) : Lp ℝ 2 haar) p.2) ∂(Measure.prod haar haar) := by
                exact hRaw
    _ = ∫ p : Cfg × Cfg,
          K t p.1 p.2 * (psi p.1 * psi p.2) ∂(Measure.prod haar haar) := by
            apply integral_congr_ae
            filter_upwards [hFirst, hSecond] with p h1 h2
            rw [h1, h2]

/-- STRICT physical Hilbert quadratic positivity of the original
FULL two-boundary Wilson kernel at EVERY positive fine coupling,
for all genuine Gauss-law sources having nonzero continuous L²
representatives. This keeps the TRUE original spatial halfweights. -/
theorem p4Q2OY_originalPhysicalWilson_quadratic_pos
    (t : ℝ) (ht : 0 < t) (f : Phys) (psi : C(Cfg, ℝ))
    (hRep : (fun A : Cfg => ((f : Phys) : Lp ℝ 2 haar) A) =ᵐ[haar] psi)
    (hpsi : psi ≠ 0) :
    0 < inner ℝ (Raw t ht.le f) f := by
  have hPos :=
    p4Q2LJ_originalFullWilsonOneSlabHaarQuadratic_pos H psi hpsi t ht
  rw [p4Q2LI_originalFullSpatialPairHaarMomentCLM_apply] at hPos
  change
    0 < (∫ p : Cfg × Cfg,
      K t p.1 p.2 * (psi p.1 * psi p.2) ∂(Measure.prod haar haar)) at hPos
  rw [p4Q2OY_originalPhysicalWilson_inner_eq_originalContinuousHaarDouble
    H t ht.le f psi hRep]
  exact hPos

/-- An actual continuous signed Gauss-law source cannot lie in the
kernel of the original positive-fine physical Wilson transfer. -/
theorem p4Q2OY_originalPhysicalWilson_transfer_ne_zero
    (t : ℝ) (ht : 0 < t) (f : Phys) (psi : C(Cfg, ℝ))
    (hRep : (fun A : Cfg => ((f : Phys) : Lp ℝ 2 haar) A) =ᵐ[haar] psi)
    (hpsi : psi ≠ 0) :
    Raw t ht.le f ≠ 0 := by
  intro hZero
  have hInner := congrArg (fun g : Phys => inner ℝ g f) hZero
  have hInnerZero : inner ℝ (Raw t ht.le f) f = 0 := by
    simpa using hInner
  exact (ne_of_gt (p4Q2OY_originalPhysicalWilson_quadratic_pos
    H t ht f psi hRep hpsi)) hInnerZero

end OriginalWilsonTruePhysicalPositiveEnergy

section ActualRightKrylovPositiveFine
variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n : ℕ)
local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Phys" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule Hn 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure Hn 2
local notation "U" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector Hn 2
local notation "Fine" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    Hn 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
local notation "Raw" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    Hn 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
local notation "Right" =>
  physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "S" => p4Q2HJ_actualRightPhysicalSourceSynthesis
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n

/-- Strict actual original positive-fine Wilson physical quadratic
energy on EVERY physically nonzero finite right-Krylov synthesis,
with NO restriction on depth, frozen beta or a Schur collapse branch. -/
theorem p4Q2OY_actualPositiveFine_allDepth_originalPhysicalEnergy_pos
    (ht : 0 < beta (n + 1)) (r : ℕ)
    (a : Fin (r + 1) → ℝ) (hSource : S r a ≠ 0) :
    0 < inner ℝ (Raw (S r a)) (S r a) := by
  obtain ⟨psi, hRep, _hGauge⟩ :=
    p4Q2OW_actualAllDepth_source_hasGaugeContinuousRepresentative
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a
  have hpsi : psi ≠ 0 :=
    p4Q2OT_originalContinuousRepresentative_ne_zero Hn
      (S r a) hSource psi hRep
  exact p4Q2OY_originalPhysicalWilson_quadratic_pos
    Hn (beta (n + 1)) ht (S r a) psi hRep hpsi

/-- The original NORMALIZED fine Wilson one-slab physical transfer
cannot annihilate any nonzero physical right-Krylov source, for
every finite H and genuine positive fine coupling. -/
theorem p4Q2OY_actualPositiveFine_allDepth_normalizedTransfer_ne_zero
    (ht : 0 < beta (n + 1)) (r : ℕ)
    (a : Fin (r + 1) → ℝ) (hSource : S r a ≠ 0) :
    Fine (S r a) ≠ 0 := by
  have hEnergy :=
    p4Q2OY_actualPositiveFine_allDepth_originalPhysicalEnergy_pos
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n ht r a hSource
  have hRawNonzero : Raw (S r a) ≠ 0 := by
    intro hZero
    have hZeroInner : inner ℝ (Raw (S r a)) (S r a) = 0 := by
      rw [hZero]
      simp
    exact (ne_of_gt hEnergy) hZeroInner
  intro hFineZero
  have hNormNonzero :
      ‖Raw‖⁻¹ ≠ 0 :=
    inv_ne_zero
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
        Hn 2 specialUnitaryTwoWilsonRankPositive
        (beta (n + 1)) (hbeta (n + 1))).ne'
  change ‖Raw‖⁻¹ • Raw (S r a) = 0 at hFineZero
  have hRawZero : Raw (S r a) = 0 := by
    exact (smul_eq_zero.mp hFineZero).resolve_left hNormNonzero
  exact hRawNonzero hRawZero

/-- The GENUINE original positive-fine Wilson right-Krylov coefficient
physical kernel is invariant under a one-step mode SHIFT.
This is an unconditional analytic no-annihilation consequence of the
STRICT complete original one-slab Wilson kernel, not a claim that
arbitrary Krylov coefficients are independent. -/
theorem p4Q2OY_actualPositiveFine_allDepth_shiftedPhysicalKernel_iff
    (ht : 0 < beta (n + 1)) (r : ℕ)
    (a : Fin (r + 1) → ℝ) :
    (∑ j : Fin (r + 1), a j • Right n ((j : ℕ) + 1) = 0) ↔
      S r a = 0 := by
  have hShift :
      Fine (S r a) = ∑ j : Fin (r + 1), a j • Right n ((j : ℕ) + 1) := by
    change Fine (∑ j : Fin (r + 1), a j • (Fine ^ (j : ℕ)) U) =
      ∑ j : Fin (r + 1), a j • (Fine ^ ((j : ℕ) + 1)) U
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [map_smul, pow_succ']
    rfl
  constructor
  · intro hZero
    by_contra hSource
    have hFineNe :=
      p4Q2OY_actualPositiveFine_allDepth_normalizedTransfer_ne_zero
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n ht r a hSource
    exact hFineNe (hShift.trans hZero)
  · intro hZero
    rw [← hShift, hZero]
    simp

end ActualRightKrylovPositiveFine
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OY_originalPhysicalWilson_inner_eq_originalContinuousHaarDouble
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OY_originalPhysicalWilson_quadratic_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OY_originalPhysicalWilson_transfer_ne_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OY_actualPositiveFine_allDepth_originalPhysicalEnergy_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OY_actualPositiveFine_allDepth_normalizedTransfer_ne_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OY_actualPositiveFine_allDepth_shiftedPhysicalKernel_iff
