import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterRemainderBanachDependentPiFiniteRootedBlockHierarchyToleranceClosure
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalRealResolventJointParameterRemainderBanachDependentPiBlockHierarchyTolerancePackage

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

variable {V ι τ β : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable [Fintype ι] [Fintype τ] [Fintype β]
variable [DecidableEq β]
variable {W : ι → Type*}
variable [∀ i, NormedAddCommGroup (W i)] [∀ i, NormedSpace ℝ (W i)]

/-- Canonical compact arbitrary finite-depth rooted hierarchy master at the
definitionally exact physical half-mass threshold. -/
noncomputable def VacuumSemigroupGapSlope.CanonicalJointRemainderCompactDependentPiFiniteRootedBlockHierarchyToleranceMasterOrder
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {taylorOrder directions : ℕ}
    (C : G.CanonicalJointRemainderCompactSharpCertificateData
      (V := V) T hInnerSymmetric taylorOrder directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (Htree : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β)
    (epsilonCarrier : ℝ) (epsilonBundle : τ → ℝ)
    (epsilonBlock : τ → β → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) : ℕ :=
  C.dependentPiFiniteRootedBlockHierarchyToleranceMasterOrder
    φ Htree epsilonCarrier epsilonBundle epsilonBlock
    epsilonCoordinate epsilonTrace

/-- Canonical compact all-node rooted hierarchy certificate after arbitrary
finite-dimensional compression at exactly `G.mass / 2`. -/
abbrev VacuumSemigroupGapSlope.CanonicalJointRemainderCompactSharpCertificateData.eventually_dependentPiFiniteRootedBlockHierarchyToleranceMaster_norm_lt
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {taylorOrder directions : ℕ}
    (C : G.CanonicalJointRemainderCompactSharpCertificateData
      (V := V) T hInnerSymmetric taylorOrder directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (Htree : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β)
    (tailOrder : ℕ) (epsilonCarrier : ℝ) (epsilonBundle : τ → ℝ)
    (epsilonBlock : τ → β → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ)
    (hCarrier : 0 < epsilonCarrier)
    (hBundle : ∀ t, 0 < epsilonBundle t)
    (hBlock : ∀ t b, 0 < epsilonBlock t b)
    (hCoordinate : ∀ i, 0 < epsilonCoordinate i)
    (hTrace : 0 < epsilonTrace) :=
  ContinuousLinearMapOpenTaylorStrongLimitData.JointRemainderCompactSharpCertificateData.eventually_dependentPiFiniteRootedBlockHierarchyToleranceMaster_norm_lt
    C φ Htree tailOrder epsilonCarrier epsilonBundle epsilonBlock
    epsilonCoordinate epsilonTrace
    hCarrier hBundle hBlock hCoordinate hTrace

/-- Canonical closed-box arbitrary finite-depth rooted hierarchy master. The
generic closed-box gap is definitionally exactly `G.mass / 2`. -/
noncomputable def VacuumSemigroupGapSlope.CanonicalJointRemainderClosedBoxDependentPiFiniteRootedBlockHierarchyToleranceMasterOrder
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {γ : Type*} {n : Filter γ} {directions : ℕ}
    (C : G.CanonicalJointRemainderClosedBoxSharpCertificateData
      (V := V) T hInnerSymmetric n directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (Htree : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β)
    (epsilonCarrier : ℝ) (epsilonBundle : τ → ℝ)
    (epsilonBlock : τ → β → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) : ℕ :=
  C.dependentPiFiniteRootedBlockHierarchyToleranceMasterOrder
    φ Htree epsilonCarrier epsilonBundle epsilonBlock
    epsilonCoordinate epsilonTrace

/-- Canonical arbitrary-joint-net all-node rooted hierarchy certificate after
arbitrary finite-dimensional compression. -/
abbrev VacuumSemigroupGapSlope.CanonicalJointRemainderClosedBoxSharpCertificateData.eventually_dependentPiFiniteRootedBlockHierarchyToleranceMaster_norm_lt
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {γ : Type*} {n : Filter γ} {directions : ℕ}
    (C : G.CanonicalJointRemainderClosedBoxSharpCertificateData
      (V := V) T hInnerSymmetric n directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (Htree : ContinuousLinearMapJointDependentPiFiniteRootedBlockHierarchy ι τ β)
    (tailOrder : ℕ) (epsilonCarrier : ℝ) (epsilonBundle : τ → ℝ)
    (epsilonBlock : τ → β → ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ)
    (hCarrier : 0 < epsilonCarrier)
    (hBundle : ∀ t, 0 < epsilonBundle t)
    (hBlock : ∀ t b, 0 < epsilonBlock t b)
    (hCoordinate : ∀ i, 0 < epsilonCoordinate i)
    (hTrace : 0 < epsilonTrace) :=
  ContinuousLinearMapOpenTaylorStrongLimitData.JointRemainderClosedBoxSharpCertificateData.eventually_dependentPiFiniteRootedBlockHierarchyToleranceMaster_norm_lt
    C φ Htree tailOrder epsilonCarrier epsilonBundle epsilonBlock
    epsilonCoordinate epsilonTrace
    hCarrier hBundle hBlock hCoordinate hTrace

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData
end MathlibAnalytic
end MGAP4D
