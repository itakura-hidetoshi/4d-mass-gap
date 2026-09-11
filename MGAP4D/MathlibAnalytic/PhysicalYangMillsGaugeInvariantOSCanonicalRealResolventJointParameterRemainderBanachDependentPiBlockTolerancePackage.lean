import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterRemainderBanachDependentPiBlockToleranceClosure
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalRealResolventJointParameterRemainderBanachDependentPiProductTolerancePackage

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

variable {V ι κ : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable [Fintype ι] [Fintype κ] [DecidableEq κ]
variable {W : ι → Type*}
variable [∀ i, NormedAddCommGroup (W i)] [∀ i, NormedSpace ℝ (W i)]

/-- Canonical compact block-tolerance master at the definitionally exact
physical half-mass threshold. -/
noncomputable def VacuumSemigroupGapSlope.CanonicalJointRemainderCompactDependentPiBlockToleranceMasterOrder
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {taylorOrder directions : ℕ}
    (C : G.CanonicalJointRemainderCompactSharpCertificateData
      (V := V) T hInnerSymmetric taylorOrder directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i) (blockOf : ι → κ)
    (epsilonCarrier epsilonBundle : ℝ)
    (epsilonBlock : κ → ℝ) (epsilonCoordinate : ι → ℝ)
    (epsilonTrace : ℝ) : ℕ :=
  C.dependentPiBlockToleranceMasterOrder φ blockOf epsilonCarrier
    epsilonBundle epsilonBlock epsilonCoordinate epsilonTrace

/-- Canonical compact block-response comparison. -/
abbrev VacuumSemigroupGapSlope.CanonicalJointRemainderCompactSharpCertificateData.responseOrder_block_le_dependentPiBlockToleranceMaster
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {taylorOrder directions : ℕ}
    (C : G.CanonicalJointRemainderCompactSharpCertificateData
      (V := V) T hInnerSymmetric taylorOrder directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i) (blockOf : ι → κ) (b : κ)
    (epsilonCarrier epsilonBundle : ℝ)
    (epsilonBlock : κ → ℝ) (epsilonCoordinate : ι → ℝ)
    (epsilonTrace : ℝ) :=
  ContinuousLinearMapOpenTaylorStrongLimitData.JointRemainderCompactSharpCertificateData.responseOrder_block_le_dependentPiBlockToleranceMaster
    C φ blockOf b epsilonCarrier epsilonBundle epsilonBlock epsilonCoordinate epsilonTrace

/-- Canonical compact original-coordinate comparison. -/
abbrev VacuumSemigroupGapSlope.CanonicalJointRemainderCompactSharpCertificateData.responseOrder_coord_le_dependentPiBlockToleranceMaster
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {taylorOrder directions : ℕ}
    (C : G.CanonicalJointRemainderCompactSharpCertificateData
      (V := V) T hInnerSymmetric taylorOrder directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i) (blockOf : ι → κ) (i : ι)
    (epsilonCarrier epsilonBundle : ℝ)
    (epsilonBlock : κ → ℝ) (epsilonCoordinate : ι → ℝ)
    (epsilonTrace : ℝ) :=
  ContinuousLinearMapOpenTaylorStrongLimitData.JointRemainderCompactSharpCertificateData.responseOrder_coord_le_dependentPiBlockToleranceMaster
    C φ blockOf i epsilonCarrier epsilonBundle epsilonBlock epsilonCoordinate epsilonTrace

/-- Canonical compact five-channel block certificate after arbitrary finite
dimensional compression at exactly `G.mass / 2`. -/
abbrev VacuumSemigroupGapSlope.CanonicalJointRemainderCompactSharpCertificateData.eventually_dependentPiBlockToleranceMaster_norm_lt
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {taylorOrder directions : ℕ}
    (C : G.CanonicalJointRemainderCompactSharpCertificateData
      (V := V) T hInnerSymmetric taylorOrder directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i) (blockOf : ι → κ)
    (tailOrder : ℕ) (epsilonCarrier epsilonBundle : ℝ)
    (epsilonBlock : κ → ℝ) (epsilonCoordinate : ι → ℝ)
    (epsilonTrace : ℝ)
    (hCarrier : 0 < epsilonCarrier) (hBundle : 0 < epsilonBundle)
    (hBlock : ∀ b, 0 < epsilonBlock b)
    (hCoordinate : ∀ i, 0 < epsilonCoordinate i)
    (hTrace : 0 < epsilonTrace) :=
  ContinuousLinearMapOpenTaylorStrongLimitData.JointRemainderCompactSharpCertificateData.eventually_dependentPiBlockToleranceMaster_norm_lt
    C φ blockOf tailOrder epsilonCarrier epsilonBundle epsilonBlock
    epsilonCoordinate epsilonTrace hCarrier hBundle hBlock hCoordinate hTrace

/-- Canonical compact block master agrees with the previous product master
when block tolerances are no stricter than the product tolerance. -/
abbrev VacuumSemigroupGapSlope.CanonicalJointRemainderCompactSharpCertificateData.dependentPiBlockToleranceMasterOrder_eq_productMaster
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {taylorOrder directions : ℕ}
    (C : G.CanonicalJointRemainderCompactSharpCertificateData
      (V := V) T hInnerSymmetric taylorOrder directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i) (blockOf : ι → κ)
    (epsilonCarrier epsilonProduct : ℝ)
    (epsilonBlock : κ → ℝ) (epsilonCoordinate : ι → ℝ)
    (epsilonTrace : ℝ)
    (hProduct : 0 < epsilonProduct) (hBlock : ∀ b, 0 < epsilonBlock b)
    (hRelax : ∀ b, epsilonProduct ≤ epsilonBlock b) :=
  ContinuousLinearMapOpenTaylorStrongLimitData.JointRemainderCompactSharpCertificateData.dependentPiBlockToleranceMasterOrder_eq_productMaster
    C φ blockOf epsilonCarrier epsilonProduct epsilonBlock epsilonCoordinate
    epsilonTrace hProduct hBlock hRelax

/-- Canonical arbitrary-joint-net closed-box block master at the exact physical
half-mass threshold. -/
noncomputable def VacuumSemigroupGapSlope.CanonicalJointRemainderClosedBoxDependentPiBlockToleranceMasterOrder
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {γ : Type*} {n : Filter γ} {directions : ℕ}
    (C : G.CanonicalJointRemainderClosedBoxSharpCertificateData
      (V := V) T hInnerSymmetric n directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i) (blockOf : ι → κ)
    (epsilonCarrier epsilonBundle : ℝ)
    (epsilonBlock : κ → ℝ) (epsilonCoordinate : ι → ℝ)
    (epsilonTrace : ℝ) : ℕ :=
  C.dependentPiBlockToleranceMasterOrder φ blockOf epsilonCarrier
    epsilonBundle epsilonBlock epsilonCoordinate epsilonTrace

/-- Canonical closed-box block-response comparison. -/
abbrev VacuumSemigroupGapSlope.CanonicalJointRemainderClosedBoxSharpCertificateData.responseOrder_block_le_dependentPiBlockToleranceMaster
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {γ : Type*} {n : Filter γ} {directions : ℕ}
    (C : G.CanonicalJointRemainderClosedBoxSharpCertificateData
      (V := V) T hInnerSymmetric n directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i) (blockOf : ι → κ) (b : κ)
    (epsilonCarrier epsilonBundle : ℝ)
    (epsilonBlock : κ → ℝ) (epsilonCoordinate : ι → ℝ)
    (epsilonTrace : ℝ) :=
  ContinuousLinearMapOpenTaylorStrongLimitData.JointRemainderClosedBoxSharpCertificateData.responseOrder_block_le_dependentPiBlockToleranceMaster
    C φ blockOf b epsilonCarrier epsilonBundle epsilonBlock epsilonCoordinate epsilonTrace

/-- Canonical closed-box original-coordinate comparison. -/
abbrev VacuumSemigroupGapSlope.CanonicalJointRemainderClosedBoxSharpCertificateData.responseOrder_coord_le_dependentPiBlockToleranceMaster
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {γ : Type*} {n : Filter γ} {directions : ℕ}
    (C : G.CanonicalJointRemainderClosedBoxSharpCertificateData
      (V := V) T hInnerSymmetric n directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i) (blockOf : ι → κ) (i : ι)
    (epsilonCarrier epsilonBundle : ℝ)
    (epsilonBlock : κ → ℝ) (epsilonCoordinate : ι → ℝ)
    (epsilonTrace : ℝ) :=
  ContinuousLinearMapOpenTaylorStrongLimitData.JointRemainderClosedBoxSharpCertificateData.responseOrder_coord_le_dependentPiBlockToleranceMaster
    C φ blockOf i epsilonCarrier epsilonBundle epsilonBlock epsilonCoordinate epsilonTrace

/-- Canonical arbitrary-joint-net closed-box five-channel block certificate.
The generic gap remains definitionally exactly `G.mass / 2`. -/
abbrev VacuumSemigroupGapSlope.CanonicalJointRemainderClosedBoxSharpCertificateData.eventually_dependentPiBlockToleranceMaster_norm_lt
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {γ : Type*} {n : Filter γ} {directions : ℕ}
    (C : G.CanonicalJointRemainderClosedBoxSharpCertificateData
      (V := V) T hInnerSymmetric n directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i) (blockOf : ι → κ)
    (tailOrder : ℕ) (epsilonCarrier epsilonBundle : ℝ)
    (epsilonBlock : κ → ℝ) (epsilonCoordinate : ι → ℝ)
    (epsilonTrace : ℝ)
    (hCarrier : 0 < epsilonCarrier) (hBundle : 0 < epsilonBundle)
    (hBlock : ∀ b, 0 < epsilonBlock b)
    (hCoordinate : ∀ i, 0 < epsilonCoordinate i)
    (hTrace : 0 < epsilonTrace) :=
  ContinuousLinearMapOpenTaylorStrongLimitData.JointRemainderClosedBoxSharpCertificateData.eventually_dependentPiBlockToleranceMaster_norm_lt
    C φ blockOf tailOrder epsilonCarrier epsilonBundle epsilonBlock
    epsilonCoordinate epsilonTrace hCarrier hBundle hBlock hCoordinate hTrace

/-- Canonical closed-box block master agrees with the prior product master
under non-stricter block tolerances. -/
abbrev VacuumSemigroupGapSlope.CanonicalJointRemainderClosedBoxSharpCertificateData.dependentPiBlockToleranceMasterOrder_eq_productMaster
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {γ : Type*} {n : Filter γ} {directions : ℕ}
    (C : G.CanonicalJointRemainderClosedBoxSharpCertificateData
      (V := V) T hInnerSymmetric n directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i) (blockOf : ι → κ)
    (epsilonCarrier epsilonProduct : ℝ)
    (epsilonBlock : κ → ℝ) (epsilonCoordinate : ι → ℝ)
    (epsilonTrace : ℝ)
    (hProduct : 0 < epsilonProduct) (hBlock : ∀ b, 0 < epsilonBlock b)
    (hRelax : ∀ b, epsilonProduct ≤ epsilonBlock b) :=
  ContinuousLinearMapOpenTaylorStrongLimitData.JointRemainderClosedBoxSharpCertificateData.dependentPiBlockToleranceMasterOrder_eq_productMaster
    C φ blockOf epsilonCarrier epsilonProduct epsilonBlock epsilonCoordinate
    epsilonTrace hProduct hBlock hRelax

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData
end MathlibAnalytic
end MGAP4D