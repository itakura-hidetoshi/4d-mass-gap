import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportEffectiveEnergyVariationalFloorConcrete
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End Filter
open scoped InnerProductSpace lp LinearPMap Topology BigOperators

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

universe u

/-- Point energies of the actual logarithmic generator on the strictly-positive
compact spectral support.  Unlike the transfer-eigenvalue presentation, this
set is phrased directly in terms of nonzero vectors in the domain of the
partially defined logarithmic generator. -/
noncomputable def realHilbertCompactPositiveZeroSupportLogGeneratorPointEnergySet
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) (hCompact : IsCompactOperator T) (hPositive : T.IsPositive) : Set ℝ :=
  {rho | ∃ x : (realHilbertCompactPositiveZeroSupportLogGenerator
      T hCompact hPositive).domain,
    (x : realHilbertZeroEigenspaceSupport T) ≠ 0 ∧
      realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive x =
        rho • (x : realHilbertZeroEigenspaceSupport T)}

private theorem realHilbertCompactPositiveZeroSupportSpectralModeVector_domain_action_pointSpectrum
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) (hCompact : IsCompactOperator T) (hPositive : T.IsPositive)
    (mu : Eigenvalues
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)))
    (v : eigenspace
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)) mu) :
    ∃ x : (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive).domain,
      (x : realHilbertZeroEigenspaceSupport T) = (v : realHilbertZeroEigenspaceSupport T) ∧
      realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive x =
        realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu •
          (v : realHilbertZeroEigenspaceSupport T) := by
  classical
  letI : CompleteSpace (realHilbertZeroEigenspaceSupport T) :=
    (realHilbertZeroEigenspaceSupport_isClosed T).completeSpace_coe
  let U :=
    realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv
      T hCompact hPositive
  let A := realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive
  let C := realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates T hCompact hPositive
  have hUv : U (v : realHilbertZeroEigenspaceSupport T) =
      lp.single
        (E := fun nu : Eigenvalues
          (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
            Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
          eigenspace
            (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
              Module.End ℝ (realHilbertZeroEigenspaceSupport T)) nu)
        2 mu v := by
    have hsymm :
        U.symm
            (lp.single
              (E := fun nu : Eigenvalues
                (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
                  Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
                eigenspace
                  (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
                    Module.End ℝ (realHilbertZeroEigenspaceSupport T)) nu)
              2 mu v) =
          (v : realHilbertZeroEigenspaceSupport T) := by
      exact
        realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv_symm_single
          T hCompact hPositive mu v
    have h := congrArg U hsymm
    simpa using h.symm
  have hvDomain : (v : realHilbertZeroEigenspaceSupport T) ∈ A.domain := by
    change U (v : realHilbertZeroEigenspaceSupport T) ∈ C.domain
    rw [hUv]
    rw [realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates_domain_mem_iff]
    refine (memℓp_zero ?_).of_exponent_ge (by norm_num)
    refine (Set.finite_singleton mu).subset ?_
    intro nu hnu
    simp only [Set.mem_singleton_iff]
    by_contra hne
    apply hnu
    simp [hne]
  let x : A.domain := ⟨(v : realHilbertZeroEigenspaceSupport T), hvDomain⟩
  refine ⟨x, rfl, ?_⟩
  apply U.injective
  have hcoords :=
    realHilbertCompactPositiveZeroSupportLogGenerator_coordinates T hCompact hPositive x
  change U (A x) =
    U (realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu •
      (v : realHilbertZeroEigenspaceSupport T))
  rw [hcoords]
  apply lp.ext
  funext nu
  rw [realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates_apply]
  change realHilbertZeroEigenspaceSupportLogEnergy T hPositive nu •
      (U (v : realHilbertZeroEigenspaceSupport T)) nu =
    (U (realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu •
      (v : realHilbertZeroEigenspaceSupport T))) nu
  rw [hUv]
  rw [U.map_smul]
  rw [hUv]
  by_cases hnu : nu = mu
  · subst nu
    simp
  · simp [hnu]

/-- Every transfer spectral mode gives a genuine nonzero eigenvector of the
actual logarithmic generator, with its exact logarithmic energy. -/
theorem realHilbertCompactPositiveZeroSupportLogGenerator_exists_spectralMode_eigenvector
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) (hCompact : IsCompactOperator T) (hPositive : T.IsPositive)
    (mu : Eigenvalues
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T))) :
    ∃ x : (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive).domain,
      (x : realHilbertZeroEigenspaceSupport T) ≠ 0 ∧
      realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive x =
        realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu •
          (x : realHilbertZeroEigenspaceSupport T) := by
  let v := realHilbertCompactPositiveZeroSupportSpectralModeVector T hPositive mu
  obtain ⟨x, hx, hAx⟩ :=
    realHilbertCompactPositiveZeroSupportSpectralModeVector_domain_action_pointSpectrum
      T hCompact hPositive mu v
  refine ⟨x, ?_, ?_⟩
  · intro hx0
    have hv0 : (v : realHilbertZeroEigenspaceSupport T) = 0 := by
      rw [← hx]
      exact hx0
    exact (realHilbertCompactPositiveZeroSupportSpectralModeVector_ne_zero
      T hPositive mu) hv0
  · simpa [hx] using hAx

/-- Every transfer logarithmic energy is an actual point energy of the
logarithmic generator. -/
theorem realHilbertCompactPositiveZeroSupportLogEnergySet_subset_logGeneratorPointEnergySet
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) (hCompact : IsCompactOperator T) (hPositive : T.IsPositive) :
    realHilbertCompactPositiveZeroSupportLogEnergySet T hPositive ⊆
      realHilbertCompactPositiveZeroSupportLogGeneratorPointEnergySet
        T hCompact hPositive := by
  rintro rho ⟨mu, hmu⟩
  obtain ⟨x, hx, hAx⟩ :=
    realHilbertCompactPositiveZeroSupportLogGenerator_exists_spectralMode_eigenvector
      T hCompact hPositive mu
  refine ⟨x, hx, ?_⟩
  rw [← hmu]
  exact hAx

/-- Conversely, every nonzero logarithmic-generator eigenvector has a nonzero
spectral coordinate, and the coordinate formula forces its eigenvalue to be the
corresponding transfer logarithmic energy. -/
theorem realHilbertCompactPositiveZeroSupportLogGeneratorPointEnergySet_subset_logEnergySet
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) (hCompact : IsCompactOperator T) (hPositive : T.IsPositive) :
    realHilbertCompactPositiveZeroSupportLogGeneratorPointEnergySet T hCompact hPositive ⊆
      realHilbertCompactPositiveZeroSupportLogEnergySet T hPositive := by
  classical
  letI : CompleteSpace (realHilbertZeroEigenspaceSupport T) :=
    (realHilbertZeroEigenspaceSupport_isClosed T).completeSpace_coe
  let U :=
    realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv
      T hCompact hPositive
  rintro rho ⟨x, hx, hAx⟩
  have hUx : U (x : realHilbertZeroEigenspaceSupport T) ≠ 0 := by
    intro hzero
    apply hx
    apply U.injective
    simpa using hzero
  have hcoord : ∃ mu : Eigenvalues
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)),
      (U (x : realHilbertZeroEigenspaceSupport T)) mu ≠ 0 := by
    by_contra hnone
    apply hUx
    apply lp.ext
    funext mu
    by_contra hmu
    exact hnone ⟨mu, hmu⟩
  rcases hcoord with ⟨mu, hmu⟩
  have hUA := congrArg U hAx
  have hcoords :=
    realHilbertCompactPositiveZeroSupportLogGenerator_coordinates T hCompact hPositive x
  rw [hcoords] at hUA
  rw [U.map_smul] at hUA
  have hmuEq := congrArg (fun y => y mu) hUA
  have hmuEq' :
      realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu •
          (U (x : realHilbertZeroEigenspaceSupport T)) mu =
        rho • (U (x : realHilbertZeroEigenspaceSupport T)) mu := by
    simpa only [realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates_apply,
      lp.coeFn_smul, Pi.smul_apply] using hmuEq
  have hzero :
      (realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu - rho) •
        (U (x : realHilbertZeroEigenspaceSupport T)) mu = 0 := by
    calc
      (realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu - rho) •
          (U (x : realHilbertZeroEigenspaceSupport T)) mu =
        realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu •
            (U (x : realHilbertZeroEigenspaceSupport T)) mu -
          rho • (U (x : realHilbertZeroEigenspaceSupport T)) mu :=
        sub_smul _ _ _
      _ = 0 := sub_eq_zero.mpr hmuEq'
  have hscalar : realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu - rho = 0 := by
    rcases smul_eq_zero.mp hzero with h | h
    · exact h
    · exact (hmu h).elim
  exact ⟨mu, sub_eq_zero.mp hscalar⟩

/-- The point-energy set of the actual logarithmic generator is exactly the
transfer logarithmic spectrum. -/
theorem realHilbertCompactPositiveZeroSupportLogGeneratorPointEnergySet_eq_logEnergySet
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) (hCompact : IsCompactOperator T) (hPositive : T.IsPositive) :
    realHilbertCompactPositiveZeroSupportLogGeneratorPointEnergySet T hCompact hPositive =
      realHilbertCompactPositiveZeroSupportLogEnergySet T hPositive := by
  apply Set.Subset.antisymm
  · exact realHilbertCompactPositiveZeroSupportLogGeneratorPointEnergySet_subset_logEnergySet
      T hCompact hPositive
  · exact realHilbertCompactPositiveZeroSupportLogEnergySet_subset_logGeneratorPointEnergySet
      T hCompact hPositive

/-- Therefore the intrinsic logarithmic spectral floor is exactly the infimum
of the actual logarithmic generator's nonzero point energies. -/
theorem realHilbertCompactPositiveZeroSupportLogEnergyInf_eq_logGeneratorPointEnergySet_inf
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) (hCompact : IsCompactOperator T) (hPositive : T.IsPositive) :
    realHilbertCompactPositiveZeroSupportLogEnergyInf T hPositive =
      sInf (realHilbertCompactPositiveZeroSupportLogGeneratorPointEnergySet
        T hCompact hPositive) := by
  rw [realHilbertCompactPositiveZeroSupportLogEnergyInf,
    realHilbertCompactPositiveZeroSupportLogGeneratorPointEnergySet_eq_logEnergySet]

local instance logGeneratorPointSpectrumSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance logGeneratorPointSpectrumSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance logGeneratorPointSpectrumSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance logGeneratorPointSpectrumSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance logGeneratorPointSpectrumSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _
local instance logGeneratorPointSpectrumSpatialSliceHaarSFinite
    (H N : ℕ) : SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance
local instance logGeneratorPointSpectrumPairHilbertSectorComplete
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    CompleteSpace (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete H N hN beta hbeta
local instance logGeneratorPointSpectrumSpectralSupportNormedSpace
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    NormedSpace ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
  infer_instance
local instance logGeneratorPointSpectrumSpectralSupportComplete
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
  exact (realHilbertZeroEigenspaceSupport_isClosed
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
      H N hN beta hbeta 1)).completeSpace_coe

/-- Point energies of the actual one-step physical support logarithmic generator. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGeneratorPointEnergySet
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) : Set ℝ := by
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
    H N hN beta hbeta 1
  let hCompact : IsCompactOperator T :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isCompact_of_pos
      H N hN beta hbeta 1 (by norm_num)
  let hPositive : T.IsPositive :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isPositive
      H N hN beta hbeta 1
  exact realHilbertCompactPositiveZeroSupportLogGeneratorPointEnergySet T hCompact hPositive

/-- The physical point-energy set equals the previously reconstructed full
logarithmic spectrum. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGeneratorPointEnergySet_eq_logEnergySet
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGeneratorPointEnergySet
        H N hN beta hbeta =
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogEnergySet
        H N hN beta hbeta := by
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
    H N hN beta hbeta 1
  let hCompact : IsCompactOperator T :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isCompact_of_pos
      H N hN beta hbeta 1 (by norm_num)
  let hPositive : T.IsPositive :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isPositive
      H N hN beta hbeta 1
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGeneratorPointEnergySet,
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogEnergySet,
    T, hCompact, hPositive] using
    (realHilbertCompactPositiveZeroSupportLogGeneratorPointEnergySet_eq_logEnergySet
      T hCompact hPositive)

/-- The physical intrinsic spectral floor is exactly the point-spectrum infimum
of the actual one-step support logarithmic generator. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogEnergyInf_eq_logGeneratorPointEnergySet_inf
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogEnergyInf
        H N hN beta hbeta =
      sInf (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGeneratorPointEnergySet
        H N hN beta hbeta) := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogEnergyInf,
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGeneratorPointEnergySet_eq_logEnergySet]

/-- At every admissible resolvent parameter, the variational effective-energy
infimum is the point-spectrum infimum of the actual logarithmic generator. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGeneratorPointEnergySet_inf_eq_effectiveEnergyLimitSet_inf
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (hSupport : ∃ v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta, v ≠ 0)
    (lambda : ℝ)
    (hlambda : |lambda| < 2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
      H N hN beta hbeta) :
    sInf (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGeneratorPointEnergySet
        H N hN beta hbeta) =
      sInf (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportEffectiveEnergyLimitSet
        H N hN beta hbeta lambda) := by
  rw [← periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogEnergyInf_eq_logGeneratorPointEnergySet_inf]
  exact periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogEnergyInf_eq_effectiveEnergyLimitSet_inf
    H N hN beta hbeta hSupport lambda hlambda

/-- The canonical finite-volume coercive decay scale remains a rigorous lower
bound for the actual logarithmic-generator point-spectrum infimum. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGeneratorPointEnergySet_inf_ge_two_mul_finiteVolumeDecayRate
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (hSupport : ∃ v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta, v ≠ 0) :
    2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
        H N hN beta hbeta ≤
      sInf (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGeneratorPointEnergySet
        H N hN beta hbeta) := by
  rw [← periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogEnergyInf_eq_logGeneratorPointEnergySet_inf]
  exact periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogEnergyInf_ge_two_mul_finiteVolumeDecayRate
    H N hN beta hbeta hSupport

end

end MathlibAnalytic
end MGAP4D
