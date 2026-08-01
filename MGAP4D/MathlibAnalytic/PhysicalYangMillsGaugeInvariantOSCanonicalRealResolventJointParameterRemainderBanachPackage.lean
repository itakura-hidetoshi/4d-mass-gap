import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventJointParameterRemainderBanachPackage
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalRealResolventJointParameterMultilinearJetDirectionFamilyBanachCompact
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalRealResolventJointParameterMultilinearJetDirectionFamilyBanachClosedBox

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

/-- Canonical OS compact data for exact joint Fréchet--Taylor remainder tails.
The analytic gap is fixed in the type to exactly `G.mass / 2`. -/
structure VacuumSemigroupGapSlope.CanonicalJointRemainderCompactData
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope) (taylorOrder directions : ℕ) where
  hP : P.IsNormalized
  hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric
  hSelf : IsSelfAdjoint T.closedRightHamiltonian
  J : V →L[ℝ] P.VacuumOrthogonalHilbert
  Q : P.VacuumOrthogonalHilbert →L[ℝ] V
  H : G.AdmissibleRescaledDefectTime → Fin directions → (V →L[ℝ] V)
  H0 : Fin directions → (V →L[ℝ] V)
  hH : Tendsto H G.admissibleRescaledDefectTimeFilter (𝓝 H0)
  ds : ℝ
  h : Fin directions → ℝ
  K : Set ℝ
  hKcompact : IsCompact K
  upper : ℝ
  hKupper : K ⊆ Set.Iic upper
  hupper : upper < G.mass / 2
  Z : Set ℝ
  baseMargin : ℝ
  endMargin : ℝ
  hbaseMargin : 0 < baseMargin
  hendMargin : 0 < endMargin
  hlimitBaseMargin : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
    baseMargin ≤ |continuousLinearMapCharacteristicDeterminant
      (continuousLinearMapCompression J Q
        (_root_.iteratedDeriv k.1
          (G.vacuumOrthogonalContinuumTaylorResolvent
            T hP hInnerSymmetric hSelf) lambda)) z|
  hlimitEndMargin : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
    endMargin ≤ |continuousLinearMapCharacteristicDeterminant
      (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k.1
            (G.vacuumOrthogonalContinuumTaylorResolvent
              T hP hInnerSymmetric hSelf) lambda) +
        continuousLinearMapJointSpectralOperatorRemainderIncrement
          directions H0 ds h) z|
  Mbase : ℝ
  Mend : ℝ
  hMbase : 0 ≤ Mbase
  hMend : 0 ≤ Mend
  hlimitBaseNorm : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
    continuousLinearMapRealResolventNorm
      (continuousLinearMapCompression J Q
        (_root_.iteratedDeriv k.1
          (G.vacuumOrthogonalContinuumTaylorResolvent
            T hP hInnerSymmetric hSelf) lambda)) z ≤ Mbase
  hlimitEndNorm : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
    continuousLinearMapRealResolventNorm
      (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k.1
            (G.vacuumOrthogonalContinuumTaylorResolvent
              T hP hInnerSymmetric hSelf) lambda) +
        continuousLinearMapJointSpectralOperatorRemainderIncrement
          directions H0 ds h) z ≤ Mend

/-- Forget the canonical provenance while retaining the exact half-mass gap. -/
def VacuumSemigroupGapSlope.CanonicalJointRemainderCompactData.toGeneric
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope} {taylorOrder directions : ℕ}
    (C : G.CanonicalJointRemainderCompactData T taylorOrder directions) :
    ContinuousLinearMapOpenTaylorStrongLimitData.JointRemainderCompactData
      (α := G.AdmissibleRescaledDefectTime)
      (E := P.VacuumOrthogonalHilbert) (V := V)
      (l := G.admissibleRescaledDefectTimeFilter) (gap := G.mass / 2)
      (F := G.admissibleRescaledDefectTaylorResolvent T C.hInnerSymmetric)
      taylorOrder directions where
  S := G.canonicalRescaledDefectTaylorStrongLimitData
    T C.hP C.hInnerSymmetric C.hSelf
  B := G.admissibleRescaledDefectOpenResolventNormBoundFamilyData
    T C.hInnerSymmetric
  L := G.vacuumOrthogonalContinuumOpenResolventNormBoundData
    T C.hP C.hInnerSymmetric C.hSelf
  hLgap := rfl
  hLresolvent := rfl
  J := C.J
  Q := C.Q
  H := C.H
  H0 := C.H0
  hH := C.hH
  ds := C.ds
  h := C.h
  K := C.K
  hKcompact := C.hKcompact
  upper := C.upper
  hKupper := C.hKupper
  hupper := C.hupper
  Z := C.Z
  baseMargin := C.baseMargin
  endMargin := C.endMargin
  hbaseMargin := C.hbaseMargin
  hendMargin := C.hendMargin
  hlimitBaseMargin := C.hlimitBaseMargin
  hlimitEndMargin := C.hlimitEndMargin
  Mbase := C.Mbase
  Mend := C.Mend
  hMbase := C.hMbase
  hMend := C.hMend
  hlimitBaseNorm := C.hlimitBaseNorm
  hlimitEndNorm := C.hlimitEndNorm

/-- Canonical OS compact carrier exact-remainder stability. -/
theorem VacuumSemigroupGapSlope.CanonicalJointRemainderCompactData.carrier_tendsto
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope} {taylorOrder directions : ℕ}
    (C : G.CanonicalJointRemainderCompactData T taylorOrder directions)
    (baseOrder tailOrder : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :=
  C.toGeneric.carrier_tendsto baseOrder tailOrder epsilon hepsilon

/-- Canonical OS compact arbitrary Banach-valued exact-remainder stability. -/
theorem VacuumSemigroupGapSlope.CanonicalJointRemainderCompactData.response_tendsto
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope} {taylorOrder directions : ℕ}
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (C : G.CanonicalJointRemainderCompactData T taylorOrder directions)
    (φ : (V →L[ℝ] V) →L[ℝ] W) (baseOrder tailOrder : ℕ)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :=
  C.toGeneric.response_tendsto φ baseOrder tailOrder epsilon hepsilon

/-- Canonical OS compact basis-independent trace exact-remainder stability. -/
theorem VacuumSemigroupGapSlope.CanonicalJointRemainderCompactData.trace_tendsto
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope} {taylorOrder directions : ℕ}
    (C : G.CanonicalJointRemainderCompactData T taylorOrder directions)
    (baseOrder tailOrder : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :=
  C.toGeneric.trace_tendsto baseOrder tailOrder epsilon hepsilon

/-- Canonical OS arbitrary joint-net closed-box data, again with the analytic
gap fixed to exactly `G.mass / 2`. -/
structure VacuumSemigroupGapSlope.CanonicalJointRemainderClosedBoxData
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope) {β : Type*} (n : Filter β)
    (directions : ℕ) where
  hP : P.IsNormalized
  hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric
  hSelf : IsSelfAdjoint T.closedRightHamiltonian
  J : V →L[ℝ] P.VacuumOrthogonalHilbert
  Q : P.VacuumOrthogonalHilbert →L[ℝ] V
  time : β → G.AdmissibleRescaledDefectTime
  degree : β → ℕ
  htime : Tendsto time n G.admissibleRescaledDefectTimeFilter
  hdegree : Tendsto degree n atTop
  H : β → Fin directions → (V →L[ℝ] V)
  H0 : Fin directions → (V →L[ℝ] V)
  hH : Tendsto H n (𝓝 H0)
  ds : ℝ
  h : Fin directions → ℝ
  box : ContinuousLinearMapClosedTaylorParameterBox (G.mass / 2)
  Z : Set ℝ
  baseMargin : ℝ
  endMargin : ℝ
  hbaseMargin : 0 < baseMargin
  hendMargin : 0 < endMargin
  hlimitBaseMargin : ∀ p, box.Contains p → ∀ z ∈ Z,
    baseMargin ≤ |continuousLinearMapCharacteristicDeterminant
      (continuousLinearMapCompression J Q
        ((G.vacuumOrthogonalContinuumTaylorResolvent
          T hP hInnerSymmetric hSelf) p.target)) z|
  hlimitEndMargin : ∀ p, box.Contains p → ∀ z ∈ Z,
    endMargin ≤ |continuousLinearMapCharacteristicDeterminant
      (continuousLinearMapCompression J Q
          ((G.vacuumOrthogonalContinuumTaylorResolvent
            T hP hInnerSymmetric hSelf) p.target) +
        continuousLinearMapJointSpectralOperatorRemainderIncrement
          directions H0 ds h) z|
  Mbase : ℝ
  Mend : ℝ
  hMbase : 0 ≤ Mbase
  hMend : 0 ≤ Mend
  hlimitBaseNorm : ∀ p, box.Contains p → ∀ z ∈ Z,
    continuousLinearMapRealResolventNorm
      (continuousLinearMapCompression J Q
        ((G.vacuumOrthogonalContinuumTaylorResolvent
          T hP hInnerSymmetric hSelf) p.target)) z ≤ Mbase
  hlimitEndNorm : ∀ p, box.Contains p → ∀ z ∈ Z,
    continuousLinearMapRealResolventNorm
      (continuousLinearMapCompression J Q
          ((G.vacuumOrthogonalContinuumTaylorResolvent
            T hP hInnerSymmetric hSelf) p.target) +
        continuousLinearMapJointSpectralOperatorRemainderIncrement
          directions H0 ds h) z ≤ Mend

/-- Forget canonical provenance of a closed-box package while preserving the
half-mass gap and the complete no-rate joint net. -/
def VacuumSemigroupGapSlope.CanonicalJointRemainderClosedBoxData.toGeneric
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope} {β : Type*} {n : Filter β}
    {directions : ℕ}
    (C : G.CanonicalJointRemainderClosedBoxData T n directions) :
    ContinuousLinearMapOpenTaylorStrongLimitData.JointRemainderClosedBoxData
      (α := G.AdmissibleRescaledDefectTime) (β := β)
      (E := P.VacuumOrthogonalHilbert) (V := V)
      (l := G.admissibleRescaledDefectTimeFilter) (gap := G.mass / 2)
      (F := G.admissibleRescaledDefectTaylorResolvent T C.hInnerSymmetric)
      (n := n) directions where
  S := G.canonicalRescaledDefectTaylorStrongLimitData
    T C.hP C.hInnerSymmetric C.hSelf
  B := G.admissibleRescaledDefectOpenResolventNormBoundFamilyData
    T C.hInnerSymmetric
  L := G.vacuumOrthogonalContinuumOpenResolventNormBoundData
    T C.hP C.hInnerSymmetric C.hSelf
  hLgap := rfl
  hLresolvent := rfl
  J := C.J
  Q := C.Q
  time := C.time
  degree := C.degree
  htime := C.htime
  hdegree := C.hdegree
  H := C.H
  H0 := C.H0
  hH := C.hH
  ds := C.ds
  h := C.h
  box := C.box
  Z := C.Z
  baseMargin := C.baseMargin
  endMargin := C.endMargin
  hbaseMargin := C.hbaseMargin
  hendMargin := C.hendMargin
  hlimitBaseMargin := C.hlimitBaseMargin
  hlimitEndMargin := C.hlimitEndMargin
  Mbase := C.Mbase
  Mend := C.Mend
  hMbase := C.hMbase
  hMend := C.hMend
  hlimitBaseNorm := C.hlimitBaseNorm
  hlimitEndNorm := C.hlimitEndNorm

/-- Canonical OS arbitrary joint-net and diagonal no-rate carrier stability. -/
theorem VacuumSemigroupGapSlope.CanonicalJointRemainderClosedBoxData.carrier_tendsto
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope} {β : Type*} {n : Filter β}
    {directions : ℕ}
    (C : G.CanonicalJointRemainderClosedBoxData T n directions)
    (baseOrder tailOrder : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :=
  C.toGeneric.carrier_diagonal_noRate baseOrder tailOrder epsilon hepsilon

/-- Canonical OS arbitrary Banach-valued joint-net and diagonal stability. -/
theorem VacuumSemigroupGapSlope.CanonicalJointRemainderClosedBoxData.response_tendsto
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope} {β W : Type*} {n : Filter β}
    [NormedAddCommGroup W] [NormedSpace ℝ W] {directions : ℕ}
    (C : G.CanonicalJointRemainderClosedBoxData T n directions)
    (φ : (V →L[ℝ] V) →L[ℝ] W) (baseOrder tailOrder : ℕ)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :=
  C.toGeneric.response_diagonal_noRate φ baseOrder tailOrder epsilon hepsilon

/-- Canonical OS basis-independent trace joint-net and diagonal stability. -/
theorem VacuumSemigroupGapSlope.CanonicalJointRemainderClosedBoxData.trace_tendsto
    {T : P.StronglyContinuousPhysicalSemigroup}
    {G : T.VacuumSemigroupGapSlope} {β : Type*} {n : Filter β}
    {directions : ℕ}
    (C : G.CanonicalJointRemainderClosedBoxData T n directions)
    (baseOrder tailOrder : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :=
  C.toGeneric.trace_diagonal_noRate baseOrder tailOrder epsilon hepsilon

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData
end MathlibAnalytic
end MGAP4D
