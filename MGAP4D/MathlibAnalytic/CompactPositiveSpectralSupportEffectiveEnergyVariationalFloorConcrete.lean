import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportEffectiveEnergyVisibleEdgeIdentificationConcrete
import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGenerator
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End Filter
open scoped InnerProductSpace lp LinearPMap Topology BigOperators

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

universe u

/-- The full logarithmic spectrum carried by the strictly-positive spectral
support of a compact positive operator. -/
noncomputable def realHilbertCompactPositiveZeroSupportLogEnergySet
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) (hPositive : T.IsPositive) : Set ℝ :=
  {rho | ∃ mu : Eigenvalues
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)),
    realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu = rho}

/-- The intrinsic lower logarithmic spectral edge of the strictly-positive
support. -/
noncomputable def realHilbertCompactPositiveZeroSupportLogEnergyInf
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) (hPositive : T.IsPositive) : ℝ :=
  sInf (realHilbertCompactPositiveZeroSupportLogEnergySet T hPositive)

/-- Every state-visible logarithmic energy belongs to the full support
logarithmic spectrum. -/
theorem realHilbertCompactPositiveZeroSupportVisibleLogEnergySet_subset_logEnergySet
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) (hCompact : IsCompactOperator T) (hPositive : T.IsPositive)
    (v : realHilbertZeroEigenspaceSupport T) :
    realHilbertCompactPositiveZeroSupportVisibleLogEnergySet T hCompact hPositive v ⊆
      realHilbertCompactPositiveZeroSupportLogEnergySet T hPositive := by
  rintro rho ⟨mu, hmu, henergy⟩
  exact ⟨mu, henergy⟩

/-- A canonical nonzero vector in a chosen positive support eigenspace. -/
noncomputable def realHilbertCompactPositiveZeroSupportSpectralModeVector
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) (hPositive : T.IsPositive)
    (mu : Eigenvalues
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T))) :
    eigenspace
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)) mu :=
  ⟨Classical.choose mu.property.exists_hasUnifEigenvector,
    (Classical.choose_spec mu.property.exists_hasUnifEigenvector).1⟩

/-- The canonical chosen spectral-mode vector is nonzero. -/
theorem realHilbertCompactPositiveZeroSupportSpectralModeVector_ne_zero
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) (hPositive : T.IsPositive)
    (mu : Eigenvalues
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T))) :
    (realHilbertCompactPositiveZeroSupportSpectralModeVector T hPositive mu :
      realHilbertZeroEigenspaceSupport T) ≠ 0 := by
  exact (Classical.choose_spec mu.property.exists_hasUnifEigenvector).2

/-- A chosen support eigenspace vector belongs to the actual logarithmic-generator
domain, where the generator acts by its exact logarithmic energy. -/
private theorem realHilbertCompactPositiveZeroSupportSpectralModeVector_domain_action
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
  let F := fun nu : Eigenvalues
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
    eigenspace
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)) nu
  have hUv : U (v : realHilbertZeroEigenspaceSupport T) =
      lp.single (E := F) 2 mu v := by
    have h := congrArg U
      (realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv_symm_single
        T hCompact hPositive mu v)
    simpa [U, F] using h.symm
  have hvDomain : (v : realHilbertZeroEigenspaceSupport T) ∈ A.domain := by
    change U (v : realHilbertZeroEigenspaceSupport T) ∈ C.domain
    rw [hUv]
    rw [realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates_domain_mem_iff]
    let hsingle : lp F 2 :=
      lp.single (E := F) 2 mu
        (realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu • v)
    have hweighted :
        (fun nu =>
          realHilbertZeroEigenspaceSupportLogEnergy T hPositive nu • Pi.single mu v nu) =
        (fun nu =>
          Pi.single mu
            (realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu • v) nu) := by
      funext nu
      by_cases hnu : nu = mu
      · subst nu
        simp
      · simp [hnu]
    rw [hweighted]
    simpa [F, hsingle] using hsingle.property
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

/-- A state concentrated in one transfer eigenspace sees exactly one
logarithmic energy. -/
theorem realHilbertCompactPositiveZeroSupportVisibleLogEnergySet_spectralModeVector
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) (hCompact : IsCompactOperator T) (hPositive : T.IsPositive)
    (mu : Eigenvalues
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T))) :
    realHilbertCompactPositiveZeroSupportVisibleLogEnergySet T hCompact hPositive
        (realHilbertCompactPositiveZeroSupportSpectralModeVector T hPositive mu) =
      {realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu} := by
  let v0 := realHilbertCompactPositiveZeroSupportSpectralModeVector T hPositive mu
  let v : realHilbertZeroEigenspaceSupport T := v0
  have hv : v ≠ 0 := by
    simpa [v, v0] using
      realHilbertCompactPositiveZeroSupportSpectralModeVector_ne_zero T hPositive mu
  obtain ⟨x, hxv, hAx⟩ :=
    realHilbertCompactPositiveZeroSupportSpectralModeVector_domain_action
      T hCompact hPositive mu v0
  have hnonempty :=
    (realHilbertCompactPositiveZeroSupportVisibleLogEnergySet_nonempty_iff
      T hCompact hPositive v).2 hv
  ext rho
  constructor
  · rintro ⟨nu, hnu, henergy⟩
    have hmode :=
      realHilbertCompactPositiveZeroSupportVisibleLogEnergy_eq_of_domain_eigenmode
        T hCompact hPositive v
        (realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu)
        x (by simpa [v] using hxv) (by simpa [v] using hAx) nu hnu
    simp only [mem_singleton_iff]
    exact henergy.symm.trans hmode
  · intro hrho
    simp only [mem_singleton_iff] at hrho
    rcases hnonempty with ⟨eta, heta⟩
    rcases heta with ⟨nu, hnu, henergy⟩
    have hmode :=
      realHilbertCompactPositiveZeroSupportVisibleLogEnergy_eq_of_domain_eigenmode
        T hCompact hPositive v
        (realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu)
        x (by simpa [v] using hxv) (by simpa [v] using hAx) nu hnu
    have hetaEq : eta = realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu :=
      henergy.symm.trans hmode
    subst rho
    rw [← hetaEq]
    exact ⟨nu, hnu, henergy⟩

/-- On a pure spectral mode, the visible lower edge is the exact logarithmic
energy of that mode. -/
theorem realHilbertCompactPositiveZeroSupportVisibleLogEnergyInf_spectralModeVector
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) (hCompact : IsCompactOperator T) (hPositive : T.IsPositive)
    (mu : Eigenvalues
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T))) :
    realHilbertCompactPositiveZeroSupportVisibleLogEnergyInf T hCompact hPositive
        (realHilbertCompactPositiveZeroSupportSpectralModeVector T hPositive mu) =
      realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu := by
  rw [realHilbertCompactPositiveZeroSupportVisibleLogEnergyInf,
    realHilbertCompactPositiveZeroSupportVisibleLogEnergySet_spectralModeVector]
  simp

/-- The set of lower logarithmic edges seen by all nonzero support states. -/
noncomputable def realHilbertCompactPositiveZeroSupportVisibleLogEnergyInfSet
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) (hCompact : IsCompactOperator T) (hPositive : T.IsPositive) : Set ℝ :=
  {rho | ∃ v : realHilbertZeroEigenspaceSupport T, v ≠ 0 ∧
    realHilbertCompactPositiveZeroSupportVisibleLogEnergyInf T hCompact hPositive v = rho}

/-- Nontrivial positive support is equivalent to nonempty full logarithmic
spectrum. -/
theorem realHilbertCompactPositiveZeroSupportLogEnergySet_nonempty_iff
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) (hCompact : IsCompactOperator T) (hPositive : T.IsPositive) :
    (realHilbertCompactPositiveZeroSupportLogEnergySet T hPositive).Nonempty ↔
      ∃ v : realHilbertZeroEigenspaceSupport T, v ≠ 0 := by
  constructor
  · rintro ⟨rho, mu, hmu⟩
    exact ⟨realHilbertCompactPositiveZeroSupportSpectralModeVector T hPositive mu,
      realHilbertCompactPositiveZeroSupportSpectralModeVector_ne_zero T hPositive mu⟩
  · rintro ⟨v, hv⟩
    obtain ⟨rho, hrho⟩ :=
      (realHilbertCompactPositiveZeroSupportVisibleLogEnergySet_nonempty_iff
        T hCompact hPositive v).2 hv
    exact ⟨rho,
      realHilbertCompactPositiveZeroSupportVisibleLogEnergySet_subset_logEnergySet
        T hCompact hPositive v hrho⟩

/-- Every full support logarithmic spectral value is realized exactly as the
visible lower edge of a nonzero pure spectral state. -/
theorem realHilbertCompactPositiveZeroSupportLogEnergySet_subset_visibleLogEnergyInfSet
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) (hCompact : IsCompactOperator T) (hPositive : T.IsPositive) :
    realHilbertCompactPositiveZeroSupportLogEnergySet T hPositive ⊆
      realHilbertCompactPositiveZeroSupportVisibleLogEnergyInfSet T hCompact hPositive := by
  rintro rho ⟨mu, henergy⟩
  refine ⟨realHilbertCompactPositiveZeroSupportSpectralModeVector T hPositive mu,
    realHilbertCompactPositiveZeroSupportSpectralModeVector_ne_zero T hPositive mu, ?_⟩
  exact (realHilbertCompactPositiveZeroSupportVisibleLogEnergyInf_spectralModeVector
    T hCompact hPositive mu).trans henergy

/-- If all positive-support logarithmic energies have a common lower bound,
then the full support spectral floor is the infimum of the visible floors over
all nonzero states. -/
theorem realHilbertCompactPositiveZeroSupportLogEnergyInf_eq_visibleLogEnergyInfSet_inf
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) (hCompact : IsCompactOperator T) (hPositive : T.IsPositive)
    (c : ℝ)
    (hLower : ∀ mu : Eigenvalues
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)),
      c ≤ realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu)
    (hSupport : ∃ v : realHilbertZeroEigenspaceSupport T, v ≠ 0) :
    realHilbertCompactPositiveZeroSupportLogEnergyInf T hPositive =
      sInf (realHilbertCompactPositiveZeroSupportVisibleLogEnergyInfSet
        T hCompact hPositive) := by
  let S := realHilbertCompactPositiveZeroSupportLogEnergySet T hPositive
  let V := realHilbertCompactPositiveZeroSupportVisibleLogEnergyInfSet T hCompact hPositive
  have hSnonempty : S.Nonempty := by
    simpa [S] using
      (realHilbertCompactPositiveZeroSupportLogEnergySet_nonempty_iff
        T hCompact hPositive).2 hSupport
  have hSbdd : BddBelow S := by
    refine ⟨c, ?_⟩
    rintro rho ⟨mu, hmu⟩
    exact hmu ▸ hLower mu
  have hSV : S ⊆ V := by
    simpa [S, V] using
      realHilbertCompactPositiveZeroSupportLogEnergySet_subset_visibleLogEnergyInfSet
        T hCompact hPositive
  have hVnonempty : V.Nonempty := hSnonempty.mono hSV
  have hFloorLeVisible : ∀ rho ∈ V, sInf S ≤ rho := by
    rintro rho ⟨v, hv, hvrho⟩
    have hVstateNonempty :=
      (realHilbertCompactPositiveZeroSupportVisibleLogEnergySet_nonempty_iff
        T hCompact hPositive v).2 hv
    have hsub :=
      realHilbertCompactPositiveZeroSupportVisibleLogEnergySet_subset_logEnergySet
        T hCompact hPositive v
    have hle := csInf_le_csInf hSbdd hVstateNonempty hsub
    exact hvrho ▸ hle
  have hVbdd : BddBelow V := ⟨sInf S, hFloorLeVisible⟩
  apply le_antisymm
  · change sInf S ≤ sInf V
    exact le_csInf hVnonempty hFloorLeVisible
  · change sInf V ≤ sInf S
    exact csInf_le_csInf hVbdd hSnonempty hSV

/-- The common coordinate lower bound also bounds the intrinsic full support
spectral floor. -/
theorem realHilbertCompactPositiveZeroSupportLogEnergyInf_ge
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) (hCompact : IsCompactOperator T) (hPositive : T.IsPositive)
    (c : ℝ)
    (hLower : ∀ mu : Eigenvalues
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)),
      c ≤ realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu)
    (hSupport : ∃ v : realHilbertZeroEigenspaceSupport T, v ≠ 0) :
    c ≤ realHilbertCompactPositiveZeroSupportLogEnergyInf T hPositive := by
  rw [realHilbertCompactPositiveZeroSupportLogEnergyInf]
  apply le_csInf
  · exact (realHilbertCompactPositiveZeroSupportLogEnergySet_nonempty_iff
      T hCompact hPositive).2 hSupport
  · rintro rho ⟨mu, hmu⟩
    exact hmu ▸ hLower mu

local instance effectiveEnergyVariationalFloorSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance effectiveEnergyVariationalFloorSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance effectiveEnergyVariationalFloorSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance effectiveEnergyVariationalFloorSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance effectiveEnergyVariationalFloorSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance effectiveEnergyVariationalFloorSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _
local instance effectiveEnergyVariationalFloorSpatialSliceHaarSFinite
    (H N : ℕ) : SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance
local instance effectiveEnergyVariationalFloorPairHilbertSectorComplete
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    CompleteSpace (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete H N hN beta hbeta
local instance effectiveEnergyVariationalFloorSpectralSupportNormedSpace
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    NormedSpace ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
  infer_instance
local instance effectiveEnergyVariationalFloorSpectralSupportComplete
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
  exact (realHilbertZeroEigenspaceSupport_isClosed
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
      H N hN beta hbeta 1)).completeSpace_coe

/-- Full logarithmic spectrum of the actual one-step physical positive support. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogEnergySet
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) : Set ℝ := by
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
    H N hN beta hbeta 1
  let hPositive : T.IsPositive :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isPositive
      H N hN beta hbeta 1
  exact realHilbertCompactPositiveZeroSupportLogEnergySet T hPositive

/-- Intrinsic lower logarithmic spectral edge of the actual one-step physical
positive support. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogEnergyInf
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) : ℝ :=
  sInf (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogEnergySet
    H N hN beta hbeta)

/-- All state-visible lower edges on nonzero physical support states. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportVisibleLogEnergyInfSet
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) : Set ℝ :=
  {rho | ∃ v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta, v ≠ 0 ∧
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportVisibleLogEnergyInf
      H N hN beta hbeta v = rho}

/-- The intrinsic physical support spectral floor is the variational infimum of
all nonzero-state visible spectral edges. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogEnergyInf_eq_visibleLogEnergyInfSet_inf
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (hSupport : ∃ v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta, v ≠ 0) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogEnergyInf
        H N hN beta hbeta =
      sInf (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportVisibleLogEnergyInfSet
        H N hN beta hbeta) := by
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
    H N hN beta hbeta 1
  let hCompact : IsCompactOperator T :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isCompact_of_pos
      H N hN beta hbeta 1 (by norm_num)
  let hPositive : T.IsPositive :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isPositive
      H N hN beta hbeta 1
  let c := 2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
    H N hN beta hbeta
  have hLower : ∀ mu : Eigenvalues
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)),
      c ≤ realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu := by
    intro mu
    simpa [T, c,
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportRestriction,
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralLogEnergy,
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralLogEnergy_ge_two_mul_finiteVolumeDecayRate
        H N hN beta hbeta mu)
  have h := realHilbertCompactPositiveZeroSupportLogEnergyInf_eq_visibleLogEnergyInfSet_inf
    T hCompact hPositive c hLower hSupport
  have hV :
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportVisibleLogEnergyInfSet
          H N hN beta hbeta =
        realHilbertCompactPositiveZeroSupportVisibleLogEnergyInfSet T hCompact hPositive := by
    ext rho
    constructor
    · rintro ⟨v, hv, hvrho⟩
      refine ⟨v, hv, ?_⟩
      simpa [
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportVisibleLogEnergyInf,
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportVisibleLogEnergySet,
        T, hCompact, hPositive] using hvrho
    · rintro ⟨v, hv, hvrho⟩
      refine ⟨v, hv, ?_⟩
      simpa [
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportVisibleLogEnergyInf,
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportVisibleLogEnergySet,
        T, hCompact, hPositive] using hvrho
  rw [hV]
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogEnergyInf,
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogEnergySet,
    realHilbertCompactPositiveZeroSupportLogEnergyInf,
    T, hPositive] using h

/-- The existing finite-volume coercive scale is a lower bound for the intrinsic
physical support spectral floor. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogEnergyInf_ge_two_mul_finiteVolumeDecayRate
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (hSupport : ∃ v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta, v ≠ 0) :
    2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
        H N hN beta hbeta ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogEnergyInf
        H N hN beta hbeta := by
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
    H N hN beta hbeta 1
  let hCompact : IsCompactOperator T :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isCompact_of_pos
      H N hN beta hbeta 1 (by norm_num)
  let hPositive : T.IsPositive :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isPositive
      H N hN beta hbeta 1
  let c := 2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
    H N hN beta hbeta
  have hLower : ∀ mu : Eigenvalues
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)),
      c ≤ realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu := by
    intro mu
    simpa [T, c,
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportRestriction,
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralLogEnergy,
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralLogEnergy_ge_two_mul_finiteVolumeDecayRate
        H N hN beta hbeta mu)
  have h := realHilbertCompactPositiveZeroSupportLogEnergyInf_ge
    T hCompact hPositive c hLower hSupport
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogEnergyInf,
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogEnergySet,
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport,
    realHilbertCompactPositiveZeroSupportLogEnergyInf,
    T, hPositive] using h

/-- The set of asymptotic effective-energy limits over all nonzero physical
support states, at a fixed admissible resolvent parameter. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportEffectiveEnergyLimitSet
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) (lambda : ℝ) : Set ℝ :=
  {rho | ∃ v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta, v ≠ 0 ∧
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_effectiveEnergyLimit
      H N hN beta hbeta v lambda = rho}

/-- At every admissible resolvent parameter, the family of asymptotic effective
energies is exactly the family of state-visible spectral edges. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportEffectiveEnergyLimitSet_eq_visibleLogEnergyInfSet
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) (lambda : ℝ)
    (hlambda : |lambda| < 2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportEffectiveEnergyLimitSet
        H N hN beta hbeta lambda =
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportVisibleLogEnergyInfSet
        H N hN beta hbeta := by
  ext rho
  constructor
  · rintro ⟨v, hv, hvrho⟩
    refine ⟨v, hv, ?_⟩
    exact (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_effectiveEnergyLimit_eq_visibleLogEnergyInf
      H N hN beta hbeta v hv lambda hlambda).symm.trans hvrho
  · rintro ⟨v, hv, hvrho⟩
    refine ⟨v, hv, ?_⟩
    exact (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_effectiveEnergyLimit_eq_visibleLogEnergyInf
      H N hN beta hbeta v hv lambda hlambda).trans hvrho

/-- Variational reconstruction: the intrinsic physical support spectral floor
is the infimum of the asymptotic effective energies over all nonzero support
states. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogEnergyInf_eq_effectiveEnergyLimitSet_inf
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (hSupport : ∃ v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta, v ≠ 0)
    (lambda : ℝ)
    (hlambda : |lambda| < 2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogEnergyInf
        H N hN beta hbeta =
      sInf (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportEffectiveEnergyLimitSet
        H N hN beta hbeta lambda) := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogEnergyInf_eq_visibleLogEnergyInfSet_inf
    H N hN beta hbeta hSupport]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportEffectiveEnergyLimitSet_eq_visibleLogEnergyInfSet
    H N hN beta hbeta lambda hlambda]

/-- The variational effective-energy floor is independent of the admissible
resolvent parameter as a set, not merely pointwise state by state. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportEffectiveEnergyLimitSet_parameter_independent
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) (lambda mu : ℝ)
    (hlambda : |lambda| < 2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
      H N hN beta hbeta)
    (hmu : |mu| < 2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportEffectiveEnergyLimitSet
        H N hN beta hbeta lambda =
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportEffectiveEnergyLimitSet
        H N hN beta hbeta mu := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportEffectiveEnergyLimitSet_eq_visibleLogEnergyInfSet
      H N hN beta hbeta lambda hlambda,
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportEffectiveEnergyLimitSet_eq_visibleLogEnergyInfSet
      H N hN beta hbeta mu hmu]

/-- Quantitatively, every variationally reconstructed asymptotic effective-energy
floor remains above the canonical finite-volume coercive scale. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportEffectiveEnergyLimitSet_inf_ge_two_mul_finiteVolumeDecayRate
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (hSupport : ∃ v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta, v ≠ 0)
    (lambda : ℝ)
    (hlambda : |lambda| < 2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
      H N hN beta hbeta) :
    2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
        H N hN beta hbeta ≤
      sInf (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportEffectiveEnergyLimitSet
        H N hN beta hbeta lambda) := by
  rw [← periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogEnergyInf_eq_effectiveEnergyLimitSet_inf
    H N hN beta hbeta hSupport lambda hlambda]
  exact periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogEnergyInf_ge_two_mul_finiteVolumeDecayRate
    H N hN beta hbeta hSupport

end

end MathlibAnalytic
end MGAP4D