import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonVacuumNormalizedCenteredPairNonTopProjectionNonzeroReduction
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopModeSignRigidity
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryVacuumMomentPositivity
import Mathlib.Tactic

/-!
# Strict positivity of the OS-vacuum / physical-top pair overlap

PR #5066 reduces nonvanishing of a canonical physical non-top projected
excitation to one scalar statement:

  inner (OS vacuum pair) (physical pair-top mode) != 0.

This file closes that residual directly from positivity.

The canonical-sign Wilson boundary vacuum is pointwise strictly positive.
After the exact boundary-to-two-slice coordinate isometry, its pair
representative is therefore strictly positive almost everywhere.

The selected one-slice physical top mode has one fixed sign almost everywhere
by #5011. Hence its tensor square, which is exactly the selected physical
pair-top mode, is nonnegative almost everywhere. It is nonzero because it has
unit norm.

The generic positive-L2 pairing lemma from #5012 then gives a strictly positive
vacuum/top pair overlap. Feeding this into #5066 theorem-generates a nonzero
canonical physical non-top projected excitation at every finite scale.

No transfer compatibility, vacuum/top alignment, or extra scalar assumption is
used.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Filter
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance vacuumTopOverlapTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance vacuumTopOverlapCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance vacuumTopOverlapSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance vacuumTopOverlapMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance vacuumTopOverlapBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance vacuumTopOverlapSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance vacuumTopOverlapSpatialHaarProbability (H N : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance vacuumTopOverlapPairHaarProbability (H N : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance

local instance vacuumTopOverlapSpatialHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- The concrete Wilson boundary vacuum remains strictly positive almost
everywhere after exact transport to ordered primary/antipodal slice
coordinates. -/
theorem periodicHypercubicEvenBoundaryVacuumPairL2_ae_pos
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ∀ᵐ z ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N),
      0 <
        periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry
          H N
          (periodicHypercubicEvenBoundaryVacuumL2
            H N hN beta hbeta) z := by
  let e :=
    periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H
      (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let μB := periodicHypercubicEvenBoundaryHaarMeasure H N
  let μP := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
  let vac := periodicHypercubicEvenBoundaryVacuumL2 H N hN beta hbeta
  have hE :
      periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry
          H N vac =ᵐ[μP]
        vac ∘ e.symm := by
    simpa [e, μP, vac] using
      periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry_coeFn
        H N vac
  have hmp :
      MeasurePreserving e μB μP := by
    simpa [e, μB, μP] using
      periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_measurePreserving_specialUnitaryHaar
        H N
  have hs :
      MeasurePreserving e.symm μP μB :=
    MeasurePreserving.symm e hmp
  have hVac :
      vac =ᵐ[μB]
        periodicHypercubicEvenBoundaryVacuumMoment H N hN beta hbeta := by
    simpa [vac, μB] using
      periodicHypercubicEvenBoundaryVacuumL2_coeFn
        H N hN beta hbeta
  have hVacPull :
      (fun z => vac (e.symm z)) =ᵐ[μP]
        fun z =>
          periodicHypercubicEvenBoundaryVacuumMoment
            H N hN beta hbeta (e.symm z) := by
    simpa [Function.comp_def] using hs.quasiMeasurePreserving.ae_eq hVac
  filter_upwards [hE, hVacPull] with z hEz hVz
  rw [hEz]
  change 0 < vac (e.symm z)
  rw [hVz]
  exact
    periodicHypercubicEvenBoundaryVacuumMoment_pos
      H N hN beta hbeta (e.symm z)

/-- The selected physical pair-top mode is nonnegative almost everywhere.

The one-slice selected top eigenvector has a fixed sign almost everywhere; its
tensor square is therefore nonnegative in either sign branch. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2_ae_nonnegative
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ∀ᵐ z ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N),
      0 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2
          H N hN beta hbeta z := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let omegaP :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
      H N hN beta hbeta
  let omega : Lp ℝ 2 μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopModeL2
      H N hN beta hbeta
  have homegaTop :
      omegaP ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
          H N hN beta hbeta := by
    simpa [omegaP] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_mem_topEigenspace
        H N hN beta hbeta
  have homegaNorm : ‖omegaP‖ = 1 := by
    simpa [omegaP] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_norm
        H N hN beta hbeta
  have hsign :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_unit_sign_rigidity
      H N hN beta hbeta omegaP homegaTop homegaNorm
  have hTensor :=
    realL2ExternalTensor_coeFn omega omega
  rcases hsign with hnonneg | hnonpos
  · have hfst :
        ∀ᵐ z ∂(μ.prod μ), 0 ≤ omega z.1 :=
      (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae
        (by simpa [omega, periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopModeL2]
          using hnonneg)
    have hsnd :
        ∀ᵐ z ∂(μ.prod μ), 0 ≤ omega z.2 :=
      (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae
        (by simpa [omega, periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopModeL2]
          using hnonneg)
    filter_upwards [hTensor, hfst, hsnd] with z hz h1 h2
    change 0 ≤ (realL2ExternalTensor omega omega : Lp ℝ 2 (μ.prod μ)) z
    rw [hz]
    simpa [realL2ExternalTensorFunction] using mul_nonneg h1 h2
  · have hfst :
        ∀ᵐ z ∂(μ.prod μ), omega z.1 ≤ 0 :=
      (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae
        (by simpa [omega, periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopModeL2]
          using hnonpos)
    have hsnd :
        ∀ᵐ z ∂(μ.prod μ), omega z.2 ≤ 0 :=
      (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae
        (by simpa [omega, periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopModeL2]
          using hnonpos)
    filter_upwards [hTensor, hfst, hsnd] with z hz h1 h2
    change 0 ≤ (realL2ExternalTensor omega omega : Lp ℝ 2 (μ.prod μ)) z
    rw [hz]
    simpa [realL2ExternalTensorFunction] using
      mul_nonneg_of_nonpos_of_nonpos h1 h2

/-- The concrete Wilson boundary vacuum pair has strictly positive inner
product with the selected physical pair-top mode. -/
theorem periodicHypercubicEvenBoundaryVacuumPairL2_inner_PhysicalOneSlabPairTopModeL2_pos
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    0 <
      inner ℝ
        (periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry
          H N
          (periodicHypercubicEvenBoundaryVacuumL2
            H N hN beta hbeta))
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2
          H N hN beta hbeta) := by
  let vac :=
    periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry
      H N
      (periodicHypercubicEvenBoundaryVacuumL2 H N hN beta hbeta)
  let top :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2
      H N hN beta hbeta
  have hvacPos :
      ∀ᵐ z ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N),
        0 < vac z := by
    simpa [vac] using
      periodicHypercubicEvenBoundaryVacuumPairL2_ae_pos
        H N hN beta hbeta
  have htopNonneg :
      ∀ᵐ z ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N),
        0 ≤ top z := by
    simpa [top] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2_ae_nonnegative
        H N hN beta hbeta
  have htopNe : top ≠ 0 := by
    intro hzero
    have hnorm :
        ‖top‖ = 1 := by
      simpa [top] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2_norm
          H N hN beta hbeta
    rw [hzero, norm_zero] at hnorm
    norm_num at hnorm
  simpa [vac, top] using
    realL2_inner_pos_of_ae_pos_ae_nonnegative_ne_zero
      vac top hvacPos htopNonneg htopNe

section VacuumNormalizedProjectedNonzero

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ} {hN : 0 < N} {hN2 : 2 ≤ N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))

/-- At every finite scale, the canonical-sign OS vacuum pair has strictly
positive overlap with the physical pair-top mode. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoMode_OSVacuumPair_inner_pairTop_pos
    (n : ℕ) :
    0 <
      inner ℝ
        (physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
          (S := S) (D := D) (halfExtent := halfExtent)
          (N := N) (hN := hN)
          (beta := beta) (hbeta := hbeta)
          (Q := Q.vacuumNormalized) (hInvariant := hInvariant) n)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2
          (halfExtent n) N hN (beta n) (hbeta n)) := by
  rw [
    physicalYangMillsVacuumNormalizedSUNTwoModeExplicitOSVacuumBoundaryPairL2_eq_boundaryVacuumPair
      Q hInvariant n]
  exact
    periodicHypercubicEvenBoundaryVacuumPairL2_inner_PhysicalOneSlabPairTopModeL2_pos
      (halfExtent n) N hN (beta n) (hbeta n)

/-- Therefore at every finite scale at least one of the two canonical
physical non-top projected centered Wilson excitations is nonzero. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoMode_exists_nonzero_centeredBoundaryPairNonTopProjection
    (n : ℕ) :
    ∃ k : Fin 2,
      physicalYangMillsVacuumNormalizedSUNTwoModeExplicitCenteredBoundaryPairNonTopProjection
          (hN2 := hN2) (Q := Q) (hInvariant := hInvariant) k n ≠ 0 := by
  apply
    physicalYangMillsVacuumNormalizedSUNTwoMode_exists_nonzero_centeredBoundaryPairNonTopProjection_of_vacuumPair_inner_pairTop_ne_zero
      (hN2 := hN2) Q hInvariant n
  exact
    (physicalYangMillsVacuumNormalizedSUNTwoMode_OSVacuumPair_inner_pairTop_pos
      Q hInvariant n).ne'

/-- Finite-volume endpoint: at every scale there is a concrete nonzero
projected centered excitation in the full physical non-top receiver, and it
obeys the existing uniform q0^m estimate for all powers. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoMode_exists_nonzero_nonTopProjection_with_uniform_q0
    (s : ℝ) (hs : 8 < s)
    (hcut :
      ∀ n : ℕ,
        beta n ≤
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
            s hs)
    (n : ℕ) :
    ∃ k : Fin 2,
      physicalYangMillsVacuumNormalizedSUNTwoModeExplicitCenteredBoundaryPairNonTopProjection
          (hN2 := hN2) (Q := Q) (hInvariant := hInvariant) k n ≠ 0 ∧
      ∀ m : ℕ,
        ‖(periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
            (halfExtent n) N hN (beta n) (hbeta n) ^ m)
            (physicalYangMillsVacuumNormalizedSUNTwoModeExplicitCenteredBoundaryPairNonTopProjection
              (hN2 := hN2) (Q := Q) (hInvariant := hInvariant) k n)‖ ≤
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ m *
            ‖physicalYangMillsVacuumNormalizedSUNTwoModeExplicitCenteredBoundaryPairNonTopProjection
              (hN2 := hN2) (Q := Q) (hInvariant := hInvariant) k n‖ := by
  rcases
    physicalYangMillsVacuumNormalizedSUNTwoMode_exists_nonzero_centeredBoundaryPairNonTopProjection
      (hN2 := hN2) Q hInvariant n with
    ⟨k, hk⟩
  refine ⟨k, hk, ?_⟩
  intro m
  exact
    physicalYangMillsVacuumNormalizedSUNTwoModeExplicitCenteredBoundaryPairNonTopProjection_pow_norm_le_uniform_q0
      (hN2 := hN2) Q hInvariant s hs hcut k n m

end VacuumNormalizedProjectedNonzero

end

end MathlibAnalytic
end MGAP4D
