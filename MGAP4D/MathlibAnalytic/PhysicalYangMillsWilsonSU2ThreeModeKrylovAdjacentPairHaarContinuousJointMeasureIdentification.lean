import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarContinuousVacuumPosteriorVariance
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointMeasureEquivalence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# P4-Q2-AU: canonical continuous vacuum represents the ORIGINAL Wilson joint law

AT proved a volume-independent one-link Haar-to-physical-posterior
variance comparison using the genuinely normalized raw Wilson
single-link conditional and the continuous Perron vacuum of the
ACTUAL gauge-invariant physical transfer.

The pre-existing original physical ground-state one-slab joint law
is expressed using an arbitrary Haar-L² representative of the
nonnegative top eigenvector. Its pointwise values on exceptional
fixed one-link fibers cannot be identified with a continuous
representative. Instead we prove the correct MEASURE-level bridge.

The canonical continuous Wilson vacuum Omega_c was previously proved
equal to the original physical top-vacuum L² class almost everywhere.
This equality passes separately through both spatial Haar factors,
so the original and continuous ground-state joint densities agree
for Haar-ALMOST EVERY pair of spatial boundary configurations.

Consequently the positive, CONTINUOUS literal density

  lambda^(-1) Omega_c(A) K_Wilson(A,B) Omega_c(B)

defines EXACTLY the pre-existing original physical ground-state
joint measure on the entire pair-configuration measurable space,
not merely a surrogate posterior measure. The continuous density
has Haar integral one and is strictly positive at every pair.

The equality is a statement about measures and almost-everywhere
densities. We do NOT claim pointwise equality with the old arbitrary
L² representative on exceptional fibers. Future disintegration into
target × off-target coordinates must respect this distinction.
No volume/spacing-uniform mass gap, sorry, admit, or new axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter Set
open scoped ENNReal InnerProductSpace InnerProduct

noncomputable section
set_option maxHeartbeats 2600000
set_option synthInstance.maxHeartbeats 850000

local instance p4AUGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4AUCompact (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4AUSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4AUMeasurable (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4AUBorel (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4AULinks (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Both copies of the L² vacuum representative may be replaced in a
genuine two-boundary one-slab Wilson joint weight, precisely under
the product Haar almost-everywhere relation. -/
theorem p4Q2AU_realJointWeight_aeEq_of_vacuum_aeEq
    {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [SFinite mu]
    (f g : X → ℝ) (K : X × X → ℝ) (c : ℝ)
    (hfg : f =ᵐ[mu] g) :
    (fun z : X × X => c * (f z.1 * K z * f z.2)) =ᵐ[mu.prod mu]
      (fun z : X × X => c * (g z.1 * K z * g z.2)) := by
  have hfprod : (fun z : X × X => f z.1) =ᵐ[mu.prod mu]
      (fun z : X × X => g z.1) := by
    simpa [Function.comp_def] using
      (Measure.quasiMeasurePreserving_fst (μ := mu) (ν := mu)).ae_eq hfg
  have hgprod : (fun z : X × X => f z.2) =ᵐ[mu.prod mu]
      (fun z : X × X => g z.2) := by
    simpa [Function.comp_def] using
      (Measure.quasiMeasurePreserving_snd (μ := mu) (ν := mu)).ae_eq hfg
  filter_upwards [hfprod, hgprod] with z h1 h2
  rw [h1, h2]

/-- The ACTUAL continuous physical Perron vacuum gives a real-valued
normalized one-slab joint density on the original two-boundary Haar
carrier, with no pointwise selection of the older L² quotient. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  let Omega :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
      H N hN beta hbeta
  ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖⁻¹ *
    (Omega z.1 *
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N beta z.1 z.2 * Omega z.2)

/-- This genuine physical joint density is strictly positive at EVERY
spatial-boundary pair, unlike the old quotient representative, which
is only almost-everywhere positive. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight_pos
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    0 < periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight
      H N hN beta hbeta z := by
  have hNorm :
      0 < ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos_from_uniform_kernel_floor
      H N hN beta hbeta
  have hOmegaLeft :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H N hN beta hbeta z.1
  have hOmegaRight :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H N hN beta hbeta z.2
  have hKernel :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
      H N beta z.1 z.2
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight
  exact mul_pos (inv_pos.mpr hNorm)
    (mul_pos (mul_pos hOmegaLeft hKernel) hOmegaRight)

/-- The canonical normalized genuine Wilson ground-state joint density is
jointly continuous in the full pair of boundary configurations. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight_continuous
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    Continuous
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight
        H N hN beta hbeta) := by
  have hOmega :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_continuous
      H N hN beta hbeta
  have hKernel :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
      H N beta
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight
  exact continuous_const.mul
    (((hOmega.comp continuous_fst).mul hKernel).mul
      (hOmega.comp continuous_snd))

/-- Original normalized physical one-slab joint density equals the
pointwise-continuous physical vacuum density on the COMPLETE pair-Haar
carrier, precisely almost everywhere. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight_ae_eq_continuous
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    (fun z => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
      H N hN beta hbeta z) =ᵐ[
        periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N]
      (fun z => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight
        H N hN beta hbeta z) := by
  let mu := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let f : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ :=
    fun A => (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
      H N hN beta hbeta).1 A
  let g := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
    H N hN beta hbeta
  let K : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ :=
    fun z => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
      H N beta z.1 z.2
  let c := ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta‖⁻¹
  have hfg : f =ᵐ[mu] g := by
    simpa [f, g, mu] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_ae_eq_existing
        H N hN beta hbeta).symm
  have hprod := p4Q2AU_realJointWeight_aeEq_of_vacuum_aeEq mu f g K c hfg
  change
    (fun z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
       PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
         c * (f z.1 * K z * f z.2)) =ᵐ[mu.prod mu]
    (fun z => c * (g z.1 * K z * g z.2))
  exact hprod

/-- A pointwise continuous, strictly positive expression represents
EXACTLY the previously authoritative original physical one-slab Wilson
ground-state joint measure. The older arbitrary L² quotient is not
asserted equal at every configuration: the measure identity follows
from its precise almost-everywhere relation to the continuous vacuum. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointMeasure
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    Measure
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
       PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N).withDensity
    (fun z => ENNReal.ofReal
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight
        H N hN beta hbeta z))

/-- The genuinely original physical one-slab joint law is EQUAL AS A MEASURE
to the continuous-Perron-vacuum Wilson joint law, for every finite volume.
In particular no synthetic posterior or reference state was introduced. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_eq_continuous
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
      H N hN beta hbeta =
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointMeasure
      H N hN beta hbeta := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointMeasure
  apply withDensity_congr_ae
  filter_upwards
    [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight_ae_eq_continuous
      H N hN beta hbeta] with z h
  exact congrArg ENNReal.ofReal h

/-- The actual continuous physical Wilson one-slab joint density
integrates to exactly one against the ORIGINAL pair-Haar probability,
not merely an independently normalized substitute probability. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight_integral_one
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    (∫ z, periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight
      H N hN beta hbeta z ∂
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) = 1 := by
  calc
    (∫ z, periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight
      H N hN beta hbeta z ∂
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) =
        ∫ z, periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
          H N hN beta hbeta z ∂
          periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N := by
      apply integral_congr_ae
      exact
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight_ae_eq_continuous
          H N hN beta hbeta).symm
    _ = 1 :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight_integral
        H N hN beta hbeta

/-- Canonical continuous-vacuum joint measure is a probability measure
because it is LITERALLY the existing original normalized physical
ground-state one-slab measure. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointMeasure_isProbabilityMeasure
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointMeasure
        H N hN beta hbeta) := by
  rw [← periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_eq_continuous
    H N hN beta hbeta]
  exact periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_isProbabilityMeasure
    H N hN beta hbeta

end
end MathlibAnalytic
end MGAP4D
