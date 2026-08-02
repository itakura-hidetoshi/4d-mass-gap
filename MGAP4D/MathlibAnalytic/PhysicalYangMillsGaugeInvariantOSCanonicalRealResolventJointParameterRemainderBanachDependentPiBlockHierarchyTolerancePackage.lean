import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterRemainderBanachDependentPiBlockHierarchyToleranceClosure
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalRealResolventJointParameterRemainderBanachDependentPiBlockTolerancePackage

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic
namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

variable {V ι κ λ : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable [Fintype ι] [Fintype κ] [Fintype λ]
variable [DecidableEq κ] [DecidableEq λ]
variable {W : ι → Type*}
variable [∀ i, NormedAddCommGroup (W i)] [∀ i, NormedSpace ℝ (W i)]

/-- Canonical compact two-level block hierarchy master at the definitionally
exact physical half-mass threshold. -/
noncomputable def VacuumSemigroupGapSlope.CanonicalJointRemainderCompactDependentPiBlockHierarchyToleranceMasterOrder
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {taylorOrder directions : ℕ}
    (C : G.CanonicalJointRemainderCompactSharpCertificateData
      (V := V) T hInnerSymmetric taylorOrder directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → λ)
    (epsilonCarrier epsilonBundle : ℝ)
    (epsilonFine : κ → ℝ) (epsilonCoarse : λ → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) : ℕ :=
  C.dependentPiBlockHierarchyToleranceMasterOrder φ fineOf coarseOf
    epsilonCarrier epsilonBundle epsilonFine epsilonCoarse
    epsilonCoordinate epsilonTrace

/-- Canonical compact coarse-block comparison. -/
abbrev VacuumSemigroupGapSlope.CanonicalJointRemainderCompactSharpCertificateData.responseOrder_coarseBlock_le_hierarchyToleranceMaster
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {taylorOrder directions : ℕ}
    (C : G.CanonicalJointRemainderCompactSharpCertificateData
      (V := V) T hInnerSymmetric taylorOrder directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → λ) (c : λ)
    (epsilonCarrier epsilonBundle : ℝ)
    (epsilonFine : κ → ℝ) (epsilonCoarse : λ → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) :=
  ContinuousLinearMapOpenTaylorStrongLimitData.JointRemainderCompactSharpCertificateData.responseOrder_coarseBlock_le_hierarchyToleranceMaster
    C φ fineOf coarseOf c epsilonCarrier epsilonBundle epsilonFine
    epsilonCoarse epsilonCoordinate epsilonTrace

/-- Canonical compact fine-block comparison. -/
abbrev VacuumSemigroupGapSlope.CanonicalJointRemainderCompactSharpCertificateData.responseOrder_fineBlock_le_hierarchyToleranceMaster
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {taylorOrder directions : ℕ}
    (C : G.CanonicalJointRemainderCompactSharpCertificateData
      (V := V) T hInnerSymmetric taylorOrder directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → λ) (k : κ)
    (epsilonCarrier epsilonBundle : ℝ)
    (epsilonFine : κ → ℝ) (epsilonCoarse : λ → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) :=
  ContinuousLinearMapOpenTaylorStrongLimitData.JointRemainderCompactSharpCertificateData.responseOrder_fineBlock_le_hierarchyToleranceMaster
    C φ fineOf coarseOf k epsilonCarrier epsilonBundle epsilonFine
    epsilonCoarse epsilonCoordinate epsilonTrace

/-- Canonical compact seven-channel hierarchy certificate after arbitrary
finite-dimensional compression at exactly `G.mass / 2`. -/
abbrev VacuumSemigroupGapSlope.CanonicalJointRemainderCompactSharpCertificateData.eventually_dependentPiBlockHierarchyToleranceMaster_norm_lt
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {taylorOrder directions : ℕ}
    (C : G.CanonicalJointRemainderCompactSharpCertificateData
      (V := V) T hInnerSymmetric taylorOrder directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → λ)
    (tailOrder : ℕ) (epsilonCarrier epsilonBundle : ℝ)
    (epsilonFine : κ → ℝ) (epsilonCoarse : λ → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ)
    (hCarrier : 0 < epsilonCarrier) (hBundle : 0 < epsilonBundle)
    (hFine : ∀ k, 0 < epsilonFine k)
    (hCoarse : ∀ c, 0 < epsilonCoarse c)
    (hCoordinate : ∀ i, 0 < epsilonCoordinate i)
    (hTrace : 0 < epsilonTrace) :=
  ContinuousLinearMapOpenTaylorStrongLimitData.JointRemainderCompactSharpCertificateData.eventually_dependentPiBlockHierarchyToleranceMaster_norm_lt
    C φ fineOf coarseOf tailOrder epsilonCarrier epsilonBundle epsilonFine
    epsilonCoarse epsilonCoordinate epsilonTrace
    hCarrier hBundle hFine hCoarse hCoordinate hTrace

/-- Canonical compact hierarchy collapses to its coarse master under inherited
fine-block tolerances. -/
abbrev VacuumSemigroupGapSlope.CanonicalJointRemainderCompactSharpCertificateData.dependentPiBlockHierarchyToleranceMasterOrder_eq_coarseMaster
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {taylorOrder directions : ℕ}
    (C : G.CanonicalJointRemainderCompactSharpCertificateData
      (V := V) T hInnerSymmetric taylorOrder directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → λ) (parent : κ → λ)
    (hrefines : ContinuousLinearMapJointDependentPiBlockRefines fineOf coarseOf parent)
    (epsilonCarrier epsilonBundle : ℝ)
    (epsilonFine : κ → ℝ) (epsilonCoarse : λ → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ)
    (hFine : ∀ k, 0 < epsilonFine k)
    (hCoarse : ∀ c, 0 < epsilonCoarse c)
    (hRelax : ∀ k, epsilonCoarse (parent k) ≤ epsilonFine k) :=
  ContinuousLinearMapOpenTaylorStrongLimitData.JointRemainderCompactSharpCertificateData.dependentPiBlockHierarchyToleranceMasterOrder_eq_coarseMaster
    C φ fineOf coarseOf parent hrefines epsilonCarrier epsilonBundle
    epsilonFine epsilonCoarse epsilonCoordinate epsilonTrace
    hFine hCoarse hRelax

/-- Canonical compact hierarchy agrees with the product master when both block
levels are no stricter than the common bundle tolerance. -/
abbrev VacuumSemigroupGapSlope.CanonicalJointRemainderCompactSharpCertificateData.dependentPiBlockHierarchyToleranceMasterOrder_eq_productMaster
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {taylorOrder directions : ℕ}
    (C : G.CanonicalJointRemainderCompactSharpCertificateData
      (V := V) T hInnerSymmetric taylorOrder directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → λ)
    (epsilonCarrier epsilonBundle : ℝ)
    (epsilonFine : κ → ℝ) (epsilonCoarse : λ → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ)
    (hBundle : 0 < epsilonBundle)
    (hFine : ∀ k, 0 < epsilonFine k)
    (hCoarse : ∀ c, 0 < epsilonCoarse c)
    (hFineRelax : ∀ k, epsilonBundle ≤ epsilonFine k)
    (hCoarseRelax : ∀ c, epsilonBundle ≤ epsilonCoarse c) :=
  ContinuousLinearMapOpenTaylorStrongLimitData.JointRemainderCompactSharpCertificateData.dependentPiBlockHierarchyToleranceMasterOrder_eq_productMaster
    C φ fineOf coarseOf epsilonCarrier epsilonBundle epsilonFine epsilonCoarse
    epsilonCoordinate epsilonTrace hBundle hFine hCoarse hFineRelax hCoarseRelax

/-- Canonical closed-box hierarchy master at the exact physical half-mass
threshold. -/
noncomputable def VacuumSemigroupGapSlope.CanonicalJointRemainderClosedBoxDependentPiBlockHierarchyToleranceMasterOrder
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {γ : Type*} {n : Filter γ} {directions : ℕ}
    (C : G.CanonicalJointRemainderClosedBoxSharpCertificateData
      (V := V) T hInnerSymmetric n directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → λ)
    (epsilonCarrier epsilonBundle : ℝ)
    (epsilonFine : κ → ℝ) (epsilonCoarse : λ → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) : ℕ :=
  C.dependentPiBlockHierarchyToleranceMasterOrder φ fineOf coarseOf
    epsilonCarrier epsilonBundle epsilonFine epsilonCoarse
    epsilonCoordinate epsilonTrace

/-- Canonical closed-box coarse-block comparison. -/
abbrev VacuumSemigroupGapSlope.CanonicalJointRemainderClosedBoxSharpCertificateData.responseOrder_coarseBlock_le_hierarchyToleranceMaster
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {γ : Type*} {n : Filter γ} {directions : ℕ}
    (C : G.CanonicalJointRemainderClosedBoxSharpCertificateData
      (V := V) T hInnerSymmetric n directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → λ) (c : λ)
    (epsilonCarrier epsilonBundle : ℝ)
    (epsilonFine : κ → ℝ) (epsilonCoarse : λ → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) :=
  ContinuousLinearMapOpenTaylorStrongLimitData.JointRemainderClosedBoxSharpCertificateData.responseOrder_coarseBlock_le_hierarchyToleranceMaster
    C φ fineOf coarseOf c epsilonCarrier epsilonBundle epsilonFine
    epsilonCoarse epsilonCoordinate epsilonTrace

/-- Canonical closed-box fine-block comparison. -/
abbrev VacuumSemigroupGapSlope.CanonicalJointRemainderClosedBoxSharpCertificateData.responseOrder_fineBlock_le_hierarchyToleranceMaster
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {γ : Type*} {n : Filter γ} {directions : ℕ}
    (C : G.CanonicalJointRemainderClosedBoxSharpCertificateData
      (V := V) T hInnerSymmetric n directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → λ) (k : κ)
    (epsilonCarrier epsilonBundle : ℝ)
    (epsilonFine : κ → ℝ) (epsilonCoarse : λ → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) :=
  ContinuousLinearMapOpenTaylorStrongLimitData.JointRemainderClosedBoxSharpCertificateData.responseOrder_fineBlock_le_hierarchyToleranceMaster
    C φ fineOf coarseOf k epsilonCarrier epsilonBundle epsilonFine
    epsilonCoarse epsilonCoordinate epsilonTrace

/-- Canonical arbitrary-joint-net seven-channel hierarchy certificate. The
generic gap remains definitionally exactly `G.mass / 2`. -/
abbrev VacuumSemigroupGapSlope.CanonicalJointRemainderClosedBoxSharpCertificateData.eventually_dependentPiBlockHierarchyToleranceMaster_norm_lt
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {γ : Type*} {n : Filter γ} {directions : ℕ}
    (C : G.CanonicalJointRemainderClosedBoxSharpCertificateData
      (V := V) T hInnerSymmetric n directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → λ)
    (tailOrder : ℕ) (epsilonCarrier epsilonBundle : ℝ)
    (epsilonFine : κ → ℝ) (epsilonCoarse : λ → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ)
    (hCarrier : 0 < epsilonCarrier) (hBundle : 0 < epsilonBundle)
    (hFine : ∀ k, 0 < epsilonFine k)
    (hCoarse : ∀ c, 0 < epsilonCoarse c)
    (hCoordinate : ∀ i, 0 < epsilonCoordinate i)
    (hTrace : 0 < epsilonTrace) :=
  ContinuousLinearMapOpenTaylorStrongLimitData.JointRemainderClosedBoxSharpCertificateData.eventually_dependentPiBlockHierarchyToleranceMaster_norm_lt
    C φ fineOf coarseOf tailOrder epsilonCarrier epsilonBundle epsilonFine
    epsilonCoarse epsilonCoordinate epsilonTrace
    hCarrier hBundle hFine hCoarse hCoordinate hTrace

/-- Canonical closed-box hierarchy collapses to the coarse master under
inherited fine tolerances. -/
abbrev VacuumSemigroupGapSlope.CanonicalJointRemainderClosedBoxSharpCertificateData.dependentPiBlockHierarchyToleranceMasterOrder_eq_coarseMaster
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {γ : Type*} {n : Filter γ} {directions : ℕ}
    (C : G.CanonicalJointRemainderClosedBoxSharpCertificateData
      (V := V) T hInnerSymmetric n directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → λ) (parent : κ → λ)
    (hrefines : ContinuousLinearMapJointDependentPiBlockRefines fineOf coarseOf parent)
    (epsilonCarrier epsilonBundle : ℝ)
    (epsilonFine : κ → ℝ) (epsilonCoarse : λ → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ)
    (hFine : ∀ k, 0 < epsilonFine k)
    (hCoarse : ∀ c, 0 < epsilonCoarse c)
    (hRelax : ∀ k, epsilonCoarse (parent k) ≤ epsilonFine k) :=
  ContinuousLinearMapOpenTaylorStrongLimitData.JointRemainderClosedBoxSharpCertificateData.dependentPiBlockHierarchyToleranceMasterOrder_eq_coarseMaster
    C φ fineOf coarseOf parent hrefines epsilonCarrier epsilonBundle
    epsilonFine epsilonCoarse epsilonCoordinate epsilonTrace
    hFine hCoarse hRelax

/-- Canonical closed-box hierarchy agrees with the product master under
non-stricter fine and coarse block tolerances. -/
abbrev VacuumSemigroupGapSlope.CanonicalJointRemainderClosedBoxSharpCertificateData.dependentPiBlockHierarchyToleranceMasterOrder_eq_productMaster
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {γ : Type*} {n : Filter γ} {directions : ℕ}
    (C : G.CanonicalJointRemainderClosedBoxSharpCertificateData
      (V := V) T hInnerSymmetric n directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → λ)
    (epsilonCarrier epsilonBundle : ℝ)
    (epsilonFine : κ → ℝ) (epsilonCoarse : λ → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ)
    (hBundle : 0 < epsilonBundle)
    (hFine : ∀ k, 0 < epsilonFine k)
    (hCoarse : ∀ c, 0 < epsilonCoarse c)
    (hFineRelax : ∀ k, epsilonBundle ≤ epsilonFine k)
    (hCoarseRelax : ∀ c, epsilonBundle ≤ epsilonCoarse c) :=
  ContinuousLinearMapOpenTaylorStrongLimitData.JointRemainderClosedBoxSharpCertificateData.dependentPiBlockHierarchyToleranceMasterOrder_eq_productMaster
    C φ fineOf coarseOf epsilonCarrier epsilonBundle epsilonFine epsilonCoarse
    epsilonCoordinate epsilonTrace hBundle hFine hCoarse hFineRelax hCoarseRelax

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData
end MathlibAnalytic
end MGAP4D
