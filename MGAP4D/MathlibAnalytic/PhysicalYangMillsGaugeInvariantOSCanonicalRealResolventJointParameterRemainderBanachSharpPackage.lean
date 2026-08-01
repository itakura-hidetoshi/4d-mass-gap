import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventJointParameterRemainderBanachSharpPackage
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalRealResolventJointParameterRemainderBanachPackage

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

/-- Canonical compact sharp-certificate data.  Its generic gap parameter is
definitionally the physical half-mass threshold `G.mass / 2`. -/
abbrev VacuumSemigroupGapSlope.CanonicalJointRemainderCompactSharpCertificateData
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (taylorOrder directions : ℕ) :=
  ContinuousLinearMapOpenTaylorStrongLimitData.JointRemainderCompactSharpCertificateData
    (V := V) (α := G.AdmissibleRescaledDefectTime)
    (E := P.VacuumOrthogonalHilbert)
    (l := G.admissibleRescaledDefectTimeFilter) (gap := G.mass / 2)
    (F := G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric)
    taylorOrder directions

/-- Build canonical compact sharp data from the already-integrated canonical
remainder package plus finite-compression geometric bounds. -/
def VacuumSemigroupGapSlope.CanonicalJointRemainderCompactSharpCertificateData.ofCanonicalData
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope} {taylorOrder directions : ℕ}
    (C : G.CanonicalJointRemainderCompactData (V := V)
      T taylorOrder directions)
    (q M : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hlimitPerturb : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ C.K, ∀ z ∈ C.Z,
      ‖ContinuousLinearMapOpenTaylorStrongLimitData.compressedJointRemainderBaseResolventFamily
          C.J C.Q taylorOrder
          (G.vacuumOrthogonalContinuumTaylorResolvent
            T C.hP C.hInnerSymmetric C.hSelf) lambda z k *
        continuousLinearMapJointSpectralOperatorRemainderIncrement
          directions C.H0 C.ds C.h‖ ≤ q)
    (hlimitEnd : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ C.K, ∀ z ∈ C.Z,
      ‖ContinuousLinearMapOpenTaylorStrongLimitData.compressedJointRemainderEndpointResolventFamily
          C.J C.Q taylorOrder directions
          (G.vacuumOrthogonalContinuumTaylorResolvent
            T C.hP C.hInnerSymmetric C.hSelf) lambda z C.H0 C.ds C.h k‖ ≤ M) :
    G.CanonicalJointRemainderCompactSharpCertificateData
      (V := V) T C.hInnerSymmetric taylorOrder directions where
  D := C.toGeneric
  q := q
  M := M
  hq0 := hq0
  hq1 := hq1
  hM := hM
  hlimitPerturb := hlimitPerturb
  hlimitEnd := hlimitEnd

/-- Canonical compact carrier certificate at exactly the half-mass gap. -/
theorem VacuumSemigroupGapSlope.CanonicalJointRemainderCompactSharpCertificateData.eventually_carrier_norm_lt
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {taylorOrder directions : ℕ}
    (C : G.CanonicalJointRemainderCompactSharpCertificateData
      (V := V) T hInnerSymmetric taylorOrder directions)
    (tailOrder : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) : _ :=
  C.eventually_carrier_norm_lt tailOrder epsilon hepsilon

variable {W : Type*}
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Canonical compact arbitrary-response certificate. -/
theorem VacuumSemigroupGapSlope.CanonicalJointRemainderCompactSharpCertificateData.eventually_response_norm_lt
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {taylorOrder directions : ℕ}
    (C : G.CanonicalJointRemainderCompactSharpCertificateData
      (V := V) T hInnerSymmetric taylorOrder directions)
    (φ : (V →L[ℝ] V) →L[ℝ] W)
    (tailOrder : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) : _ :=
  C.eventually_response_norm_lt φ tailOrder epsilon hepsilon

/-- Canonical compact basis-independent trace certificate. -/
theorem VacuumSemigroupGapSlope.CanonicalJointRemainderCompactSharpCertificateData.eventually_trace_norm_lt
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {taylorOrder directions : ℕ}
    (C : G.CanonicalJointRemainderCompactSharpCertificateData
      (V := V) T hInnerSymmetric taylorOrder directions)
    (tailOrder : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) : _ :=
  C.eventually_trace_norm_lt tailOrder epsilon hepsilon

/-- Canonical arbitrary-joint-net closed-box sharp-certificate data.  The gap
is again definitionally exactly `G.mass / 2`. -/
abbrev VacuumSemigroupGapSlope.CanonicalJointRemainderClosedBoxSharpCertificateData
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {β : Type*} (n : Filter β) (directions : ℕ) :=
  ContinuousLinearMapOpenTaylorStrongLimitData.JointRemainderClosedBoxSharpCertificateData
    (V := V) (α := G.AdmissibleRescaledDefectTime) (β := β)
    (E := P.VacuumOrthogonalHilbert)
    (l := G.admissibleRescaledDefectTimeFilter) (gap := G.mass / 2)
    (F := G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric)
    (n := n) directions

/-- Build canonical closed-box sharp data from the existing canonical package
and finite-compression geometric bounds. -/
def VacuumSemigroupGapSlope.CanonicalJointRemainderClosedBoxSharpCertificateData.ofCanonicalData
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope} {β : Type*} {n : Filter β}
    {directions : ℕ}
    (C : G.CanonicalJointRemainderClosedBoxData (V := V) T n directions)
    (q M : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hlimitPerturb : ∀ p, C.box.Contains p → ∀ z ∈ C.Z, ∀ k : Fin 1,
      ‖ContinuousLinearMapOpenTaylorStrongLimitData.closedBoxJointRemainderLimitBaseFamily
          C.J C.Q
          (G.vacuumOrthogonalContinuumTaylorResolvent
            T C.hP C.hInnerSymmetric C.hSelf) p z k *
        continuousLinearMapJointSpectralOperatorRemainderIncrement
          directions C.H0 C.ds C.h‖ ≤ q)
    (hlimitEnd : ∀ p, C.box.Contains p → ∀ z ∈ C.Z, ∀ k : Fin 1,
      ‖ContinuousLinearMapOpenTaylorStrongLimitData.closedBoxJointRemainderLimitEndpointFamily
          C.J C.Q directions
          (G.vacuumOrthogonalContinuumTaylorResolvent
            T C.hP C.hInnerSymmetric C.hSelf) p z C.H0 C.ds C.h k‖ ≤ M) :
    G.CanonicalJointRemainderClosedBoxSharpCertificateData
      (V := V) T C.hInnerSymmetric n directions where
  D := C.toGeneric
  q := q
  M := M
  hq0 := hq0
  hq1 := hq1
  hM := hM
  hlimitPerturb := hlimitPerturb
  hlimitEnd := hlimitEnd

/-- Canonical closed-box carrier certificate for arbitrary joint nets. -/
theorem VacuumSemigroupGapSlope.CanonicalJointRemainderClosedBoxSharpCertificateData.eventually_carrier_norm_lt
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {β : Type*} {n : Filter β} {directions : ℕ}
    (C : G.CanonicalJointRemainderClosedBoxSharpCertificateData
      (V := V) T hInnerSymmetric n directions)
    (tailOrder : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) : _ :=
  C.eventually_carrier_norm_lt tailOrder epsilon hepsilon

/-- Canonical closed-box arbitrary-response certificate. -/
theorem VacuumSemigroupGapSlope.CanonicalJointRemainderClosedBoxSharpCertificateData.eventually_response_norm_lt
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {β : Type*} {n : Filter β} {directions : ℕ}
    (C : G.CanonicalJointRemainderClosedBoxSharpCertificateData
      (V := V) T hInnerSymmetric n directions)
    (φ : (V →L[ℝ] V) →L[ℝ] W)
    (tailOrder : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) : _ :=
  C.eventually_response_norm_lt φ tailOrder epsilon hepsilon

/-- Canonical closed-box basis-independent trace certificate. -/
theorem VacuumSemigroupGapSlope.CanonicalJointRemainderClosedBoxSharpCertificateData.eventually_trace_norm_lt
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {β : Type*} {n : Filter β} {directions : ℕ}
    (C : G.CanonicalJointRemainderClosedBoxSharpCertificateData
      (V := V) T hInnerSymmetric n directions)
    (tailOrder : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) : _ :=
  C.eventually_trace_norm_lt tailOrder epsilon hepsilon

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData
end MathlibAnalytic
end MGAP4D
