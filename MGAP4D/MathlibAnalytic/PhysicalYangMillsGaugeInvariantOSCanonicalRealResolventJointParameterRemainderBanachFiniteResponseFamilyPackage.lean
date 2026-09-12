import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventJointParameterRemainderBanachFiniteResponseFamilyPackage
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalRealResolventJointParameterRemainderBanachMasterPackage

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

/-- The canonical compact finite-response-family master order at the exact
physical half-mass threshold. -/
noncomputable def VacuumSemigroupGapSlope.CanonicalJointRemainderCompactFiniteResponseFamilyMasterOrder
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {taylorOrder directions : ℕ}
    (C : G.CanonicalJointRemainderCompactSharpCertificateData
      (V := V) T hInnerSymmetric taylorOrder directions)
    (φs : List ((V →L[ℝ] V) →L[ℝ] W)) (epsilon : ℝ) : ℕ :=
  C.finiteResponseFamilyMasterOrder φs epsilon

/-- Canonical compact finite-family certificate.  Through the canonical data
abbreviation, the generic gap is definitionally exactly `G.mass / 2`. -/
abbrev VacuumSemigroupGapSlope.CanonicalJointRemainderCompactSharpCertificateData.eventually_finiteResponseFamilyMaster_norm_lt
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {taylorOrder directions : ℕ}
    (C : G.CanonicalJointRemainderCompactSharpCertificateData
      (V := V) T hInnerSymmetric taylorOrder directions)
    (φs : List ((V →L[ℝ] V) →L[ℝ] W))
    (tailOrder : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :=
  ContinuousLinearMapOpenTaylorStrongLimitData.JointRemainderCompactSharpCertificateData.eventually_finiteResponseFamilyMaster_norm_lt
    C φs tailOrder epsilon hepsilon

/-- The canonical arbitrary-joint-net closed-box finite-response-family master
order at exactly the physical half-mass threshold. -/
noncomputable def VacuumSemigroupGapSlope.CanonicalJointRemainderClosedBoxFiniteResponseFamilyMasterOrder
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {β : Type*} {n : Filter β} {directions : ℕ}
    (C : G.CanonicalJointRemainderClosedBoxSharpCertificateData
      (V := V) T hInnerSymmetric n directions)
    (φs : List ((V →L[ℝ] V) →L[ℝ] W)) (epsilon : ℝ) : ℕ :=
  C.finiteResponseFamilyMasterOrder φs epsilon

/-- Canonical closed-box finite-family certificate for arbitrary joint nets.
The underlying generic gap is definitionally exactly `G.mass / 2`. -/
abbrev VacuumSemigroupGapSlope.CanonicalJointRemainderClosedBoxSharpCertificateData.eventually_finiteResponseFamilyMaster_norm_lt
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {β : Type*} {n : Filter β} {directions : ℕ}
    (C : G.CanonicalJointRemainderClosedBoxSharpCertificateData
      (V := V) T hInnerSymmetric n directions)
    (φs : List ((V →L[ℝ] V) →L[ℝ] W))
    (tailOrder : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :=
  ContinuousLinearMapOpenTaylorStrongLimitData.JointRemainderClosedBoxSharpCertificateData.eventually_finiteResponseFamilyMaster_norm_lt
    C φs tailOrder epsilon hepsilon

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData
end MathlibAnalytic
end MGAP4D
