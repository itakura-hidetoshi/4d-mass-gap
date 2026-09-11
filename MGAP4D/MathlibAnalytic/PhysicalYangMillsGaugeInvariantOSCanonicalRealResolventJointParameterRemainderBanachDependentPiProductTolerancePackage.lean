import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventJointParameterRemainderBanachDependentPiProductTolerancePackage
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalRealResolventJointParameterRemainderBanachDependentPiProductEncodingPackage

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

variable {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

variable {ι : Type*} [Fintype ι]
variable {W : ι → Type*}
variable [∀ i, NormedAddCommGroup (W i)]
variable [∀ i, NormedSpace ℝ (W i)]

/-- The canonical compact dependent Pi-product vector-tolerance master order at
the definitionally exact physical half-mass threshold. -/
noncomputable def VacuumSemigroupGapSlope.CanonicalJointRemainderCompactDependentPiProductToleranceMasterOrder
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {taylorOrder directions : ℕ}
    (C : G.CanonicalJointRemainderCompactSharpCertificateData
      (V := V) T hInnerSymmetric taylorOrder directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (epsilonCarrier epsilonProduct : ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) : ℕ :=
  C.dependentPiProductToleranceMasterOrder
    φ epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace

/-- Canonical compact coordinate-order comparison at coordinate-specific
strict tolerances. -/
abbrev VacuumSemigroupGapSlope.CanonicalJointRemainderCompactSharpCertificateData.responseOrder_coord_le_dependentPiProductToleranceMaster
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {taylorOrder directions : ℕ}
    (C : G.CanonicalJointRemainderCompactSharpCertificateData
      (V := V) T hInnerSymmetric taylorOrder directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i) (i : ι)
    (epsilonCarrier epsilonProduct : ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) :=
  ContinuousLinearMapOpenTaylorStrongLimitData.JointRemainderCompactSharpCertificateData.responseOrder_coord_le_dependentPiProductToleranceMaster
    C φ i epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace

/-- Canonical compact dependent Pi-product vector-tolerance certificate.  One
order controls carrier, encoded product, every differently typed coordinate,
and trace after finite-dimensional compression at exactly `G.mass / 2`. -/
abbrev VacuumSemigroupGapSlope.CanonicalJointRemainderCompactSharpCertificateData.eventually_dependentPiProductToleranceMaster_norm_lt
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {taylorOrder directions : ℕ}
    (C : G.CanonicalJointRemainderCompactSharpCertificateData
      (V := V) T hInnerSymmetric taylorOrder directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (tailOrder : ℕ)
    (epsilonCarrier epsilonProduct : ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ)
    (hCarrier : 0 < epsilonCarrier)
    (hProduct : 0 < epsilonProduct)
    (hCoordinate : ∀ i, 0 < epsilonCoordinate i)
    (hTrace : 0 < epsilonTrace) :=
  ContinuousLinearMapOpenTaylorStrongLimitData.JointRemainderCompactSharpCertificateData.eventually_dependentPiProductToleranceMaster_norm_lt
    C φ tailOrder epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace
    hCarrier hProduct hCoordinate hTrace

/-- Canonical compact finite-subfamily restriction cannot increase the
vector-tolerance master. -/
abbrev VacuumSemigroupGapSlope.CanonicalJointRemainderCompactSharpCertificateData.dependentPiProductToleranceMasterOrder_subfamily_le
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {taylorOrder directions : ℕ}
    (C : G.CanonicalJointRemainderCompactSharpCertificateData
      (V := V) T hInnerSymmetric taylorOrder directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i) (s : Finset ι)
    (epsilonCarrier epsilonProduct : ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ)
    (hProduct : 0 < epsilonProduct) :=
  ContinuousLinearMapOpenTaylorStrongLimitData.JointRemainderCompactSharpCertificateData.dependentPiProductToleranceMasterOrder_subfamily_le
    C φ s epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace hProduct

/-- Canonical compact homogeneous vector-tolerance master is invariant when
observables and coordinate tolerances are reindexed together. -/
abbrev VacuumSemigroupGapSlope.CanonicalJointRemainderCompactSharpCertificateData.dependentPiProductToleranceMasterOrder_reindex_eq
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {taylorOrder directions responseCount : ℕ}
    (C : G.CanonicalJointRemainderCompactSharpCertificateData
      (V := V) T hInnerSymmetric taylorOrder directions)
    {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (φ : Fin responseCount → ((V →L[ℝ] V) →L[ℝ] U))
    (epsilonCoordinate : Fin responseCount → ℝ)
    (e : Fin responseCount ≃ Fin responseCount)
    (epsilonCarrier epsilonProduct epsilonTrace : ℝ)
    (hProduct : 0 < epsilonProduct) :=
  ContinuousLinearMapOpenTaylorStrongLimitData.JointRemainderCompactSharpCertificateData.dependentPiProductToleranceMasterOrder_reindex_eq
    C φ epsilonCoordinate e epsilonCarrier epsilonProduct epsilonTrace hProduct

/-- The canonical arbitrary-joint-net closed-box dependent Pi-product
vector-tolerance master order at exactly the physical half-mass threshold. -/
noncomputable def VacuumSemigroupGapSlope.CanonicalJointRemainderClosedBoxDependentPiProductToleranceMasterOrder
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {β : Type*} {n : Filter β} {directions : ℕ}
    (C : G.CanonicalJointRemainderClosedBoxSharpCertificateData
      (V := V) T hInnerSymmetric n directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (epsilonCarrier epsilonProduct : ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) : ℕ :=
  C.dependentPiProductToleranceMasterOrder
    φ epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace

/-- Canonical closed-box coordinate-order comparison at coordinate-specific
strict tolerances. -/
abbrev VacuumSemigroupGapSlope.CanonicalJointRemainderClosedBoxSharpCertificateData.responseOrder_coord_le_dependentPiProductToleranceMaster
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {β : Type*} {n : Filter β} {directions : ℕ}
    (C : G.CanonicalJointRemainderClosedBoxSharpCertificateData
      (V := V) T hInnerSymmetric n directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i) (i : ι)
    (epsilonCarrier epsilonProduct : ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ) :=
  ContinuousLinearMapOpenTaylorStrongLimitData.JointRemainderClosedBoxSharpCertificateData.responseOrder_coord_le_dependentPiProductToleranceMaster
    C φ i epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace

/-- Canonical arbitrary-joint-net closed-box dependent Pi-product
vector-tolerance certificate.  The underlying generic gap remains
definitionally exactly `G.mass / 2`. -/
abbrev VacuumSemigroupGapSlope.CanonicalJointRemainderClosedBoxSharpCertificateData.eventually_dependentPiProductToleranceMaster_norm_lt
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {β : Type*} {n : Filter β} {directions : ℕ}
    (C : G.CanonicalJointRemainderClosedBoxSharpCertificateData
      (V := V) T hInnerSymmetric n directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (tailOrder : ℕ)
    (epsilonCarrier epsilonProduct : ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ)
    (hCarrier : 0 < epsilonCarrier)
    (hProduct : 0 < epsilonProduct)
    (hCoordinate : ∀ i, 0 < epsilonCoordinate i)
    (hTrace : 0 < epsilonTrace) :=
  ContinuousLinearMapOpenTaylorStrongLimitData.JointRemainderClosedBoxSharpCertificateData.eventually_dependentPiProductToleranceMaster_norm_lt
    C φ tailOrder epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace
    hCarrier hProduct hCoordinate hTrace

/-- Canonical closed-box finite-subfamily restriction cannot increase the
vector-tolerance master. -/
abbrev VacuumSemigroupGapSlope.CanonicalJointRemainderClosedBoxSharpCertificateData.dependentPiProductToleranceMasterOrder_subfamily_le
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {β : Type*} {n : Filter β} {directions : ℕ}
    (C : G.CanonicalJointRemainderClosedBoxSharpCertificateData
      (V := V) T hInnerSymmetric n directions)
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i) (s : Finset ι)
    (epsilonCarrier epsilonProduct : ℝ)
    (epsilonCoordinate : ι → ℝ) (epsilonTrace : ℝ)
    (hProduct : 0 < epsilonProduct) :=
  ContinuousLinearMapOpenTaylorStrongLimitData.JointRemainderClosedBoxSharpCertificateData.dependentPiProductToleranceMasterOrder_subfamily_le
    C φ s epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace hProduct

/-- Canonical closed-box homogeneous vector-tolerance master is invariant when
observables and coordinate tolerances are reindexed together. -/
abbrev VacuumSemigroupGapSlope.CanonicalJointRemainderClosedBoxSharpCertificateData.dependentPiProductToleranceMasterOrder_reindex_eq
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {β : Type*} {n : Filter β} {directions responseCount : ℕ}
    (C : G.CanonicalJointRemainderClosedBoxSharpCertificateData
      (V := V) T hInnerSymmetric n directions)
    {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (φ : Fin responseCount → ((V →L[ℝ] V) →L[ℝ] U))
    (epsilonCoordinate : Fin responseCount → ℝ)
    (e : Fin responseCount ≃ Fin responseCount)
    (epsilonCarrier epsilonProduct epsilonTrace : ℝ)
    (hProduct : 0 < epsilonProduct) :=
  ContinuousLinearMapOpenTaylorStrongLimitData.JointRemainderClosedBoxSharpCertificateData.dependentPiProductToleranceMasterOrder_reindex_eq
    C φ epsilonCoordinate e epsilonCarrier epsilonProduct epsilonTrace hProduct

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData
end MathlibAnalytic
end MGAP4D
