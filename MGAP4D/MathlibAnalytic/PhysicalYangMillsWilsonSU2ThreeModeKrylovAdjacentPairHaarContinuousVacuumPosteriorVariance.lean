import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarNormalizedLocalConditionalDirichlet
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumUniformDoobFactor
import Mathlib.Tactic

/-!
# P4-Q2-AT: the actual one-slab Wilson–continuous-vacuum posterior variance

AS constructed the genuine normalized one-link conditional SU(N) Haar law
from the LITERAL one-slab Wilson kernel, proving rho_raw ≥ exp(-16 beta).
The physical positive continuous top-vacuum is a canonical representative
of the *existing physical vacuum L² class*, not a surrogate Perron vector.
Its actual one-link Harnack ratio is exp(8 beta), and the existing Doob
comparison loses exp(-16 beta) after fiber normalization.

This file joins these two previously separate, genuinely physical carriers.
The posterior is the Doob transform of the AS raw one-slab conditional by
the canonical continuous physical vacuum, exactly the weight appearing in
the continuously represented original Wilson ground-state joint kernel.
We obtain, for every genuine SU(N) one-link observable X square-integrable
under both indicated one-link measures,

  exp(-32 beta) * evariance_Haar(X)
       ≤ evariance_Wilson-one-slab-continuous-vacuum-posterior(X).

The local coefficient is independent of spatial volume. This is a
ONE-LINK POSTERIOR VARIANCE bound. It is NOT a bound on the global
physical time-transfer or a continuum Yang–Mills mass gap. The earlier
arbitrary L² representative fiber is only equal to the continuous one
almost everywhere in the whole spatial carrier; exceptional fixed fibers
must NOT be silently identified with this canonical continuous law.
No new sorry, admit, axiom, Gram proxy, Dobrushin construction, or
uncertified continuum assumption is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal InnerProductSpace

noncomputable section
set_option maxHeartbeats 2600000
set_option synthInstance.maxHeartbeats 850000

local instance p4ATGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4ATCompact (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4ATSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4ATMeasurable (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4ATBorel (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4ATLinks (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The actual canonical continuous-representative physical ground-state
joint weight restricted to one right-boundary link. Unlike the old arbitrary
L²-class pointwise representative, both vacuum factors here are bona fide
continuous strictly positive physical Wilson vacuum values. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateRightLinkJointWeight
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  let Omega := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
    H N hN beta hbeta
  ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta‖⁻¹ *
    (Omega left *
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N beta left (Function.update right target g) *
      Omega (Function.update right target g))

/-- ACTUAL one-slab physical ground-state joint factorization on a right
link: the constant unmodified background Wilson kernel and left vacuum
amplitude factor out, leaving exactly the AS raw Wilson one-link
Boltzmann factor times the canonical continuous physical vacuum.
This is a literal Wilson identity, not a surrogate posterior ansatz. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateRightLinkJointWeight_eq
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateRightLinkJointWeight
        H N hN beta hbeta left right target g =
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖⁻¹ *
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H N hN beta hbeta left *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta left right)) *
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta left right target g *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta (Function.update right target g)) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateRightLinkJointWeight
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_update_right_eq_localFactor_mul]
  ring

/-- The concrete one-link physical Wilson–continuous-ground-state posterior
probability, not a generic Doob placeholder: its raw measure is exactly the
AS original one-slab kernel-normalized Haar conditional, and its weight is
exactly the existing canonical positive continuous physical Wilson vacuum
along this right-boundary link. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumOriginalWilsonPosteriorLaw
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Measure (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkDoobMeasure
    H N hN beta hbeta
    (periodicHypercubicEvenSpecialUnitaryRightTargetLocalConditionalHaarLaw
      H N beta left right target)
    right target

/-- This genuine one-link posterior is a probability measure automatically:
AS normalized the literal Wilson factor, while the physical vacuum
Harnack theorem supplies positivity/finiteness of the Doob normalization. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumOriginalWilsonPosteriorLaw_probability
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumOriginalWilsonPosteriorLaw
        H N hN beta hbeta left right target) := by
  let nu := periodicHypercubicEvenSpecialUnitaryRightTargetLocalConditionalHaarLaw
    H N beta left right target
  letI : IsProbabilityMeasure nu :=
    periodicHypercubicEvenSpecialUnitaryRightTargetLocalConditionalHaarLaw_probability
      H N beta left right target
  change IsProbabilityMeasure
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkDoobMeasure
      H N hN beta hbeta nu right target)
  infer_instance

/-- Any two true probability measures satisfying c * Haar ≤ ν obey the same
lower comparison for Mathlib's EXACT extended variance, for test functions
which are L² under both laws. This is the missing *measure order -> best
constant -> variance* bridge, independent of Wilson-specific geometry. -/
theorem p4Q2AT_evariance_lower_of_measure_domination
    {G : Type*} [MeasurableSpace G]
    (mu nu : Measure G) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (c : ℝ≥0∞) (hc : c • mu ≤ nu)
    (X : G → ℝ) (hXmu : MemLp X 2 mu) (hXnu : MemLp X 2 nu) :
    c * evariance X mu ≤ evariance X nu := by
  rw [← doobBestConstantSquaredResidual_eq_evariance mu X hXmu,
    ← doobBestConstantSquaredResidual_eq_evariance nu X hXnu]
  unfold doobBestConstantSquaredResidual
  refine le_iInf fun a => ?_
  calc
    c * (⨅ b : ℝ, doobCenteredSquaredResidual mu X b) ≤
        c * doobCenteredSquaredResidual mu X a :=
      mul_le_mul_left' (iInf_le _ a) c
    _ = ∫⁻ x, ENNReal.ofReal ((X x - a) ^ 2) ∂(c • mu) := by
      simpa [doobCenteredSquaredResidual, smul_eq_mul] using
        (lintegral_smul_measure
          (μ := mu) c (fun x => ENNReal.ofReal ((X x - a) ^ 2))).symm
    _ ≤ doobCenteredSquaredResidual nu X a := by
      exact lintegral_mono' hc le_rfl

/-- The AS raw one-slab SU(N) Wilson conditional probability dominates
Haar by the actual local coupling-dependent factor exp(-16 beta).
This controls whole measures, not only arbitrary finite samples. -/
theorem periodicHypercubicEvenSpecialUnitaryRightTargetLocalConditionalHaarLaw_dominates_Haar
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    (ENNReal.ofReal (Real.exp (-16 * beta))) •
        normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ) ≤
      periodicHypercubicEvenSpecialUnitaryRightTargetLocalConditionalHaarLaw
        H N beta left right target := by
  let mu := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let rho := periodicHypercubicEvenSpecialUnitaryRightTargetLocalHaarDensity
    H N beta left right target
  let c := ENNReal.ofReal (Real.exp (-16 * beta))
  have hdens : (fun _ : Matrix.specialUnitaryGroup (Fin N) ℂ => c) ≤ᵐ[mu]
      (fun g => ENNReal.ofReal (rho g)) := by
    exact ae_of_all mu (fun g =>
      ENNReal.ofReal_le_ofReal
        (periodicHypercubicEvenSpecialUnitaryRightTargetLocalHaarDensity_bounds
          H N hN beta hbeta left right target g).1)
  have hsource : periodicHypercubicEvenSpecialUnitaryRightTargetLocalConditionalHaarLaw
      H N beta left right target =
        mu.withDensity (fun g => ENNReal.ofReal (rho g)) := by
    exact periodicHypercubicEvenSpecialUnitaryRightTargetLocalConditionalHaarLaw_eq_withDensity
      H N beta left right target
  change c • mu ≤
    periodicHypercubicEvenSpecialUnitaryRightTargetLocalConditionalHaarLaw
      H N beta left right target
  rw [hsource]
  simpa using (withDensity_mono (μ := mu) hdens)

/-- Explicit variance Poincaré comparison of the ACTUAL AS one-link Wilson
conditional with Haar, with local and spatial-volume-independent
exp(-16 beta) coefficient. -/
theorem periodicHypercubicEvenSpecialUnitaryRightTargetLocalConditionalHaarLaw_evariance_ge_Haar
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (X : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (hHaar : MemLp X 2
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))
    (hRaw : MemLp X 2
      (periodicHypercubicEvenSpecialUnitaryRightTargetLocalConditionalHaarLaw
        H N beta left right target)) :
    ENNReal.ofReal (Real.exp (-16 * beta)) *
        evariance X (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) ≤
      evariance X
        (periodicHypercubicEvenSpecialUnitaryRightTargetLocalConditionalHaarLaw
          H N beta left right target) := by
  let mu := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let nu := periodicHypercubicEvenSpecialUnitaryRightTargetLocalConditionalHaarLaw
    H N beta left right target
  letI : IsProbabilityMeasure mu := by dsimp [mu]; infer_instance
  letI : IsProbabilityMeasure nu :=
    periodicHypercubicEvenSpecialUnitaryRightTargetLocalConditionalHaarLaw_probability
      H N beta left right target
  have hDom :
      (ENNReal.ofReal (Real.exp (-16 * beta))) • mu ≤ nu :=
    periodicHypercubicEvenSpecialUnitaryRightTargetLocalConditionalHaarLaw_dominates_Haar
      H N hN beta hbeta left right target
  exact p4Q2AT_evariance_lower_of_measure_domination
    mu nu (ENNReal.ofReal (Real.exp (-16 * beta))) hDom X hHaar hRaw

/-- The genuine one-slab Wilson continuous-vacuum posterior has a further
exact exp(-16 beta) *lower* variance comparison against the raw Wilson
one-link conditional law. This is a concrete use of the canonical
physical-vacuum pointwise Harnack theorem (not an assumed distortion). -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumOriginalWilsonPosteriorLaw_evariance_ge_raw
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (X : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (hRaw : MemLp X 2
      (periodicHypercubicEvenSpecialUnitaryRightTargetLocalConditionalHaarLaw
        H N beta left right target)) :
    ENNReal.ofReal (Real.exp (-16 * beta)) *
        evariance X
          (periodicHypercubicEvenSpecialUnitaryRightTargetLocalConditionalHaarLaw
            H N beta left right target) ≤
      evariance X
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumOriginalWilsonPosteriorLaw
          H N hN beta hbeta left right target) := by
  let nu := periodicHypercubicEvenSpecialUnitaryRightTargetLocalConditionalHaarLaw
    H N beta left right target
  letI : IsProbabilityMeasure nu :=
    periodicHypercubicEvenSpecialUnitaryRightTargetLocalConditionalHaarLaw_probability
      H N beta left right target
  have h :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkDoob_evariance_lower_bound
      H N hN beta hbeta nu right target X hRaw
  dsimp only at h
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuum_harnackENNRealRatio_eq_exp_neg_sixteen
    H N hN beta hbeta right] at h
  simpa [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumOriginalWilsonPosteriorLaw,
    nu] using h

/-- AT: FULLY CONCRETE physical one-slab Wilson canonical-continuous
ground-state POSTERIOR variance dominates SU(N) Haar variance by
exp(-32 beta), independent of spatial H. This combines the exact original
Wilson raw conditional density of AS with the physical top-vacuum Harnack
factor, via the true normalized Doob law and exact extended variances. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumOriginalWilsonPosteriorLaw_evariance_ge_Haar
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (X : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (hHaar : MemLp X 2
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))
    (hRaw : MemLp X 2
      (periodicHypercubicEvenSpecialUnitaryRightTargetLocalConditionalHaarLaw
        H N beta left right target)) :
    ENNReal.ofReal (Real.exp (-32 * beta)) *
        evariance X (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) ≤
      evariance X
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumOriginalWilsonPosteriorLaw
          H N hN beta hbeta left right target) := by
  let mu := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let nu := periodicHypercubicEvenSpecialUnitaryRightTargetLocalConditionalHaarLaw
    H N beta left right target
  let post := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumOriginalWilsonPosteriorLaw
    H N hN beta hbeta left right target
  let c : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-16 * beta))
  have hRawBound : c * evariance X mu ≤ evariance X nu :=
    periodicHypercubicEvenSpecialUnitaryRightTargetLocalConditionalHaarLaw_evariance_ge_Haar
      H N hN beta hbeta left right target X hHaar hRaw
  have hPostBound : c * evariance X nu ≤ evariance X post :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumOriginalWilsonPosteriorLaw_evariance_ge_raw
      H N hN beta hbeta left right target X hRaw
  have hExp : Real.exp (-16 * beta) * Real.exp (-16 * beta) =
      Real.exp (-32 * beta) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hCoeff : c * c = ENNReal.ofReal (Real.exp (-32 * beta)) := by
    dsimp [c]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact congrArg ENNReal.ofReal hExp
  calc
    ENNReal.ofReal (Real.exp (-32 * beta)) * evariance X mu =
        c * (c * evariance X mu) := by
          rw [← hCoeff]
          mul_assoc
    _ ≤ c * evariance X nu := mul_le_mul_left' hRawBound c
    _ ≤ evariance X post := hPostBound

end
end MathlibAnalytic
end MGAP4D
