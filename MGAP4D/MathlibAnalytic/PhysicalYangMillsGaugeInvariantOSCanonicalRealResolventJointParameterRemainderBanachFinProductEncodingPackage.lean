import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventJointParameterRemainderBanachFinProductEncodingPackage
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalRealResolventJointParameterRemainderBanachFiniteResponseFamilyPackage

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

variable {W : Type*}
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The canonical compact finite-product master order at the exact physical
half-mass threshold. -/
noncomputable def VacuumSemigroupGapSlope.CanonicalJointRemainderCompactFinProductMasterOrder
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {taylorOrder directions responseCount : ℕ}
    (C : G.CanonicalJointRemainderCompactSharpCertificateData
      (V := V) T hInnerSymmetric taylorOrder directions)
    (φ : Fin responseCount → ((V →L[ℝ] V) →L[ℝ] W))
    (epsilon : ℝ) : ℕ :=
  C.finProductMasterOrder φ epsilon

/-- Canonical compact order comparison: the coordinate-family master order is
bounded by the single finite-product master order at definitionally exact
`G.mass / 2`. -/
abbrev VacuumSemigroupGapSlope.CanonicalJointRemainderCompactSharpCertificateData.finiteResponseFamilyMasterOrder_ofFn_le_finProductMaster
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {taylorOrder directions responseCount : ℕ}
    (C : G.CanonicalJointRemainderCompactSharpCertificateData
      (V := V) T hInnerSymmetric taylorOrder directions)
    (φ : Fin responseCount → ((V →L[ℝ] V) →L[ℝ] W))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :=
  ContinuousLinearMapOpenTaylorStrongLimitData.JointRemainderCompactSharpCertificateData.finiteResponseFamilyMasterOrder_ofFn_le_finProductMaster
    C φ epsilon hepsilon

/-- Canonical compact finite-product certificate.  One order controls the
carrier, encoded finite product, every coordinate response, and trace after
finite-dimensional compression at the exact half-mass threshold. -/
abbrev VacuumSemigroupGapSlope.CanonicalJointRemainderCompactSharpCertificateData.eventually_finProductMaster_norm_lt
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {taylorOrder directions responseCount : ℕ}
    (C : G.CanonicalJointRemainderCompactSharpCertificateData
      (V := V) T hInnerSymmetric taylorOrder directions)
    (φ : Fin responseCount → ((V →L[ℝ] V) →L[ℝ] W))
    (tailOrder : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :=
  ContinuousLinearMapOpenTaylorStrongLimitData.JointRemainderCompactSharpCertificateData.eventually_finProductMaster_norm_lt
    C φ tailOrder epsilon hepsilon

/-- The canonical arbitrary-joint-net closed-box finite-product master order at
exactly the physical half-mass threshold. -/
noncomputable def VacuumSemigroupGapSlope.CanonicalJointRemainderClosedBoxFinProductMasterOrder
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {β : Type*} {n : Filter β} {directions responseCount : ℕ}
    (C : G.CanonicalJointRemainderClosedBoxSharpCertificateData
      (V := V) T hInnerSymmetric n directions)
    (φ : Fin responseCount → ((V →L[ℝ] V) →L[ℝ] W))
    (epsilon : ℝ) : ℕ :=
  C.finProductMasterOrder φ epsilon

/-- Canonical closed-box order comparison at the exact physical half-mass
threshold. -/
abbrev VacuumSemigroupGapSlope.CanonicalJointRemainderClosedBoxSharpCertificateData.finiteResponseFamilyMasterOrder_ofFn_le_finProductMaster
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {β : Type*} {n : Filter β} {directions responseCount : ℕ}
    (C : G.CanonicalJointRemainderClosedBoxSharpCertificateData
      (V := V) T hInnerSymmetric n directions)
    (φ : Fin responseCount → ((V →L[ℝ] V) →L[ℝ] W))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :=
  ContinuousLinearMapOpenTaylorStrongLimitData.JointRemainderClosedBoxSharpCertificateData.finiteResponseFamilyMasterOrder_ofFn_le_finProductMaster
    C φ epsilon hepsilon

/-- Canonical arbitrary-joint-net closed-box finite-product certificate.  The
underlying generic gap is definitionally exactly `G.mass / 2`. -/
abbrev VacuumSemigroupGapSlope.CanonicalJointRemainderClosedBoxSharpCertificateData.eventually_finProductMaster_norm_lt
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {β : Type*} {n : Filter β} {directions responseCount : ℕ}
    (C : G.CanonicalJointRemainderClosedBoxSharpCertificateData
      (V := V) T hInnerSymmetric n directions)
    (φ : Fin responseCount → ((V →L[ℝ] V) →L[ℝ] W))
    (tailOrder : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :=
  ContinuousLinearMapOpenTaylorStrongLimitData.JointRemainderClosedBoxSharpCertificateData.eventually_finProductMaster_norm_lt
    C φ tailOrder epsilon hepsilon

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData
end MathlibAnalytic
end MGAP4D
