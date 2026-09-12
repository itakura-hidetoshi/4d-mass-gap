import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventJointParameterRemainderBanachTransportProductPackage
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

variable {W X : Type*}
variable [NormedAddCommGroup W] [NormedSpace ℝ W]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The canonical compact binary-product master order at the exact physical
half-mass threshold. -/
noncomputable def VacuumSemigroupGapSlope.CanonicalJointRemainderCompactBinaryProductMasterOrder
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {taylorOrder directions : ℕ}
    (C : G.CanonicalJointRemainderCompactSharpCertificateData
      (V := V) T hInnerSymmetric taylorOrder directions)
    (φ : (V →L[ℝ] V) →L[ℝ] W)
    (θ : (V →L[ℝ] V) →L[ℝ] X)
    (epsilon : ℝ) : ℕ :=
  C.binaryProductMasterOrder φ θ epsilon

/-- Canonical compact transport certificate.  The original finite-family
master order controls all responses after contraction postcomposition, and the
generic gap is definitionally exactly `G.mass / 2`. -/
abbrev VacuumSemigroupGapSlope.CanonicalJointRemainderCompactSharpCertificateData.eventually_finiteResponseFamilyMaster_postcompose_norm_lt
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {taylorOrder directions : ℕ}
    (C : G.CanonicalJointRemainderCompactSharpCertificateData
      (V := V) T hInnerSymmetric taylorOrder directions)
    (ψ : W →L[ℝ] X)
    (φs : List ((V →L[ℝ] V) →L[ℝ] W))
    (tailOrder : ℕ) (epsilon : ℝ)
    (hψ : ‖ψ‖ ≤ 1) (hepsilon : 0 < epsilon) :=
  ContinuousLinearMapOpenTaylorStrongLimitData.JointRemainderCompactSharpCertificateData.eventually_finiteResponseFamilyMaster_postcompose_norm_lt
    C ψ φs tailOrder epsilon hψ hepsilon

/-- Canonical compact binary-product certificate.  It simultaneously controls
the carrier, product response, both coordinate responses, and trace after
finite-dimensional compression at the exact half-mass threshold. -/
abbrev VacuumSemigroupGapSlope.CanonicalJointRemainderCompactSharpCertificateData.eventually_binaryProductMaster_norm_lt
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {taylorOrder directions : ℕ}
    (C : G.CanonicalJointRemainderCompactSharpCertificateData
      (V := V) T hInnerSymmetric taylorOrder directions)
    (φ : (V →L[ℝ] V) →L[ℝ] W)
    (θ : (V →L[ℝ] V) →L[ℝ] X)
    (tailOrder : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :=
  ContinuousLinearMapOpenTaylorStrongLimitData.JointRemainderCompactSharpCertificateData.eventually_binaryProductMaster_norm_lt
    C φ θ tailOrder epsilon hepsilon

/-- The canonical arbitrary-joint-net closed-box binary-product master order at
exactly the physical half-mass threshold. -/
noncomputable def VacuumSemigroupGapSlope.CanonicalJointRemainderClosedBoxBinaryProductMasterOrder
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {β : Type*} {n : Filter β} {directions : ℕ}
    (C : G.CanonicalJointRemainderClosedBoxSharpCertificateData
      (V := V) T hInnerSymmetric n directions)
    (φ : (V →L[ℝ] V) →L[ℝ] W)
    (θ : (V →L[ℝ] V) →L[ℝ] X)
    (epsilon : ℝ) : ℕ :=
  C.binaryProductMasterOrder φ θ epsilon

/-- Canonical arbitrary-joint-net closed-box transport certificate at the exact
physical half-mass threshold. -/
abbrev VacuumSemigroupGapSlope.CanonicalJointRemainderClosedBoxSharpCertificateData.eventually_finiteResponseFamilyMaster_postcompose_norm_lt
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {β : Type*} {n : Filter β} {directions : ℕ}
    (C : G.CanonicalJointRemainderClosedBoxSharpCertificateData
      (V := V) T hInnerSymmetric n directions)
    (ψ : W →L[ℝ] X)
    (φs : List ((V →L[ℝ] V) →L[ℝ] W))
    (tailOrder : ℕ) (epsilon : ℝ)
    (hψ : ‖ψ‖ ≤ 1) (hepsilon : 0 < epsilon) :=
  ContinuousLinearMapOpenTaylorStrongLimitData.JointRemainderClosedBoxSharpCertificateData.eventually_finiteResponseFamilyMaster_postcompose_norm_lt
    C ψ φs tailOrder epsilon hψ hepsilon

/-- Canonical arbitrary-joint-net closed-box binary-product certificate.  The
underlying generic gap is definitionally exactly `G.mass / 2`. -/
abbrev VacuumSemigroupGapSlope.CanonicalJointRemainderClosedBoxSharpCertificateData.eventually_binaryProductMaster_norm_lt
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {β : Type*} {n : Filter β} {directions : ℕ}
    (C : G.CanonicalJointRemainderClosedBoxSharpCertificateData
      (V := V) T hInnerSymmetric n directions)
    (φ : (V →L[ℝ] V) →L[ℝ] W)
    (θ : (V →L[ℝ] V) →L[ℝ] X)
    (tailOrder : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :=
  ContinuousLinearMapOpenTaylorStrongLimitData.JointRemainderClosedBoxSharpCertificateData.eventually_binaryProductMaster_norm_lt
    C φ θ tailOrder epsilon hepsilon

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData
end MathlibAnalytic
end MGAP4D
