import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorTransferEigenmode
import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorResolventTuranEqualityGeneratorEigenmodeConcrete
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End
open scoped InnerProductSpace lp LinearPMap

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

universe u

/-- The logarithmic energies actually seen by a support state in the intrinsic
Hilbert-sum spectral coordinates. -/
noncomputable def realHilbertCompactPositiveZeroSupportVisibleLogEnergySet
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) (hCompact : IsCompactOperator T) (hPositive : T.IsPositive)
    (v : realHilbertZeroEigenspaceSupport T) : Set ℝ :=
  {rho | ∃ mu : Eigenvalues
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)),
    (realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv
      T hCompact hPositive v) mu ≠ 0 ∧
    realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu = rho}

/-- A support state has a visible logarithmic energy exactly when it is nonzero. -/
theorem realHilbertCompactPositiveZeroSupportVisibleLogEnergySet_nonempty_iff
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) (hCompact : IsCompactOperator T) (hPositive : T.IsPositive)
    (v : realHilbertZeroEigenspaceSupport T) :
    (realHilbertCompactPositiveZeroSupportVisibleLogEnergySet T hCompact hPositive v).Nonempty ↔
      v ≠ 0 := by
  let U := realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv
    T hCompact hPositive
  constructor
  · rintro ⟨rho, mu, hmu, henergy⟩
    intro hv
    subst v
    apply hmu
    rfl
  · intro hv
    have hUv : U v ≠ 0 := by
      intro hz
      apply hv
      apply U.injective
      simpa using hz
    have hex : ∃ mu : Eigenvalues
        (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
          Module.End ℝ (realHilbertZeroEigenspaceSupport T)), (U v) mu ≠ 0 := by
      by_contra hnone
      push Not at hnone
      apply hUv
      apply lp.ext
      funext mu
      exact hnone mu
    rcases hex with ⟨mu, hmu⟩
    refine ⟨realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu, ?_⟩
    exact ⟨mu, by simpa [U] using hmu, rfl⟩

/-- Every visible coordinate of a genuine logarithmic-generator eigenmode has
exactly the generator eigenvalue as its logarithmic energy. -/
theorem realHilbertCompactPositiveZeroSupportVisibleLogEnergy_eq_of_domain_eigenmode
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) (hCompact : IsCompactOperator T) (hPositive : T.IsPositive)
    (v : realHilbertZeroEigenspaceSupport T) (rho : ℝ)
    (x : (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive).domain)
    (hxv : (x : realHilbertZeroEigenspaceSupport T) = v)
    (hAx : realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive x = rho • v)
    (mu : Eigenvalues
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)))
    (hmu : (realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv
      T hCompact hPositive v) mu ≠ 0) :
    realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu = rho := by
  let U := realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv
    T hCompact hPositive
  let A := realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive
  have hCoord :
      realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates T hCompact hPositive
          ⟨U (x : realHilbertZeroEigenspaceSupport T), x.property⟩ = rho • U v := by
    calc
      _ = U (A x) := by
        simpa [U, A] using
          (realHilbertCompactPositiveZeroSupportLogGenerator_coordinates
            T hCompact hPositive x).symm
      _ = U (rho • v) := by rw [hAx]
      _ = rho • U v := U.map_smul rho v
  have h := congrArg (fun y => y mu) hCoord
  have hcomponent :
      realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu • (U v) mu =
        rho • (U v) mu := by
    simpa [realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates_apply, hxv] using h
  exact smul_left_injective ℝ (by simpa [U] using hmu) hcomponent

/-- The lower edge of the logarithmic energies visible to a support state. -/
noncomputable def realHilbertCompactPositiveZeroSupportVisibleLogEnergyInf
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) (hCompact : IsCompactOperator T) (hPositive : T.IsPositive)
    (v : realHilbertZeroEigenspaceSupport T) : ℝ :=
  sInf (realHilbertCompactPositiveZeroSupportVisibleLogEnergySet T hCompact hPositive v)

local instance visibleLogEnergyEdgeConcreteSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance visibleLogEnergyEdgeConcreteSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance visibleLogEnergyEdgeConcreteSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance visibleLogEnergyEdgeConcreteSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance visibleLogEnergyEdgeConcreteSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance visibleLogEnergyEdgeConcreteSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _
local instance visibleLogEnergyEdgeConcreteSpatialSliceHaarSFinite
    (H N : ℕ) : SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance
local instance visibleLogEnergyEdgeConcretePairHilbertSectorComplete
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    CompleteSpace (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete H N hN beta hbeta

/-- State-visible logarithmic spectrum of the actual one-step physical support. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportVisibleLogEnergySet
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta) : Set ℝ := by
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
    H N hN beta hbeta 1
  let hCompact : IsCompactOperator T :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isCompact_of_pos
      H N hN beta hbeta 1 (by norm_num)
  let hPositive : T.IsPositive :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isPositive
      H N hN beta hbeta 1
  exact realHilbertCompactPositiveZeroSupportVisibleLogEnergySet T hCompact hPositive v

/-- The bottom logarithmic energy actually visible to the physical support state. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportVisibleLogEnergyInf
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta) : ℝ :=
  sInf (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportVisibleLogEnergySet
    H N hN beta hbeta v)

/-- A nonzero physical support state has nonempty state-visible logarithmic spectrum. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportVisibleLogEnergySet_nonempty
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta) (hv : v ≠ 0) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportVisibleLogEnergySet
      H N hN beta hbeta v).Nonempty := by
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
    H N hN beta hbeta 1
  let hCompact : IsCompactOperator T :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isCompact_of_pos
      H N hN beta hbeta 1 (by norm_num)
  let hPositive : T.IsPositive :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isPositive
      H N hN beta hbeta 1
  simpa [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportVisibleLogEnergySet,
    T, hCompact, hPositive] using
    (realHilbertCompactPositiveZeroSupportVisibleLogEnergySet_nonempty_iff
      T hCompact hPositive v).2 hv

end

end MathlibAnalytic
end MGAP4D