import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingBoundaryL2TransferGap
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingBoundaryL2PoincareVacuumIntegralGap
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSExponentialGapSlope

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

/-- A scale-uniform finite Wilson shared-boundary transfer package with the
concrete exponential quadratic contraction

`‖K_{n,t}‖ ≤ sqrt (exp (-mass * t))`.

This is strictly weaker as an input interface than directly assuming the
Poincaré defect inequality: the latter is generated below from the operator
norm estimate.  The model-specific obligations are the actual boundary
transfer, its intertwining with half-time OS translation, and this exponential
operator-norm contraction. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSApproximatingExponentialBoundaryL2TransferGapCertificate
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant) where
  mass : ℝ
  mass_pos : 0 < mass
  exchange : ∀ n,
    PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.PositiveTimeObservableContractionSemigroup.ReflectionTimeTranslationExchange
      (C.toPositiveTimeObservableContractionSemigroup n)
  gram_integrable :
    ∀ (n : ℕ)
      (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n).Carrier)
      (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration
        (halfExtent n) N),
      Integrable
        (periodicHypercubicEvenBoundaryObservableGramFeature
          (halfExtent n) N hN (beta n) (hbeta n)
          (fun x =>
            physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
              S D halfExtent N hN beta hbeta B hInvariant n F x)
          b)
        (periodicHypercubicEvenOpenHalfHaarMeasure (halfExtent n) N)
  boundaryMoment_memLp :
    ∀ (n : ℕ)
      (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n).Carrier),
      MemLp
        (fun b =>
          physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
            S D halfExtent N hN beta hbeta B hInvariant n F b)
        2
        (periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N)
  boundaryTransfer :
    (n : ℕ) → NNReal →
      PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N
  boundaryMoment_intertwining :
    ∀ (n : ℕ) (t : NNReal),
      let Pn :=
        physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta B hInvariant n
      let Tn := C.toPositiveTimeObservableContractionSemigroup n
      ∀ F : Pn.Carrier,
        boundaryTransfer n t
            (physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2
              S D halfExtent N hN beta hbeta B hInvariant n
              (Pn.vacuumCenteredCarrier F)
              (boundaryMoment_memLp n (Pn.vacuumCenteredCarrier F))) =
          physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2
            S D halfExtent N hN beta hbeta B hInvariant n
            (Tn.carrierTranslation (t / 2) (Pn.vacuumCenteredCarrier F))
            (boundaryMoment_memLp n
              (Tn.carrierTranslation (t / 2) (Pn.vacuumCenteredCarrier F)))
  boundaryTransfer_opNorm_le :
    ∀ (n : ℕ) (t : NNReal),
      ‖boundaryTransfer n t‖ ≤
        Real.sqrt (Real.exp (-mass * (t : ℝ)))

namespace PhysicalYangMillsEvenPeriodicWilsonOSApproximatingExponentialBoundaryL2TransferGapCertificate

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    {C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant}

/-- The exponential operator-norm package is an instance of the general
boundary transfer-gap certificate with quadratic factor `exp (-mass * t)`. -/
noncomputable def toApproximatingBoundaryL2TransferGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingExponentialBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C where
  mass := Q.mass
  mass_pos := Q.mass_pos
  quadraticDecayFactor := fun t => Real.exp (-Q.mass * (t : ℝ))
  quadraticDecayFactor_nonneg :=
    exponential_quadraticDecayFactor_nonneg Q.mass
  slope_tendsto :=
    exponential_quadraticDecayFactor_slope_tendsto Q.mass
  exchange := Q.exchange
  gram_integrable := Q.gram_integrable
  boundaryMoment_memLp := Q.boundaryMoment_memLp
  boundaryTransfer := Q.boundaryTransfer
  boundaryMoment_intertwining := Q.boundaryMoment_intertwining
  boundaryTransfer_opNorm_le := Q.boundaryTransfer_opNorm_le

/-- Exponential operator-norm contraction implies the exact Poincaré defect
inequality with defect `1 - exp (-mass * t)`. -/
noncomputable def toApproximatingBoundaryL2PoincareGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingExponentialBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2PoincareGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C where
  mass := Q.mass
  mass_pos := Q.mass_pos
  defectFactor := fun t => 1 - Real.exp (-Q.mass * (t : ℝ))
  defectFactor_nonneg :=
    exponential_defect_nonneg Q.mass_pos.le
  defectFactor_le_one :=
    exponential_defect_le_one Q.mass
  slope_tendsto := by
    simpa only [sub_sub_cancel] using
      exponential_quadraticDecayFactor_slope_tendsto Q.mass
  exchange := Q.exchange
  gram_integrable := Q.gram_integrable
  boundaryMoment_memLp := Q.boundaryMoment_memLp
  boundaryTransfer := Q.boundaryTransfer
  boundaryMoment_intertwining := Q.boundaryMoment_intertwining
  boundaryTransfer_defect_bound := by
    intro n t v
    let K := Q.boundaryTransfer n t
    let q : ℝ := Real.exp (-Q.mass * (t : ℝ))
    have hq : 0 ≤ q := by
      exact (Real.exp_pos _).le
    have hnorm : ‖K v‖ ≤ Real.sqrt q * ‖v‖ := by
      calc
        ‖K v‖ ≤ ‖K‖ * ‖v‖ := K.le_opNorm v
        _ ≤ Real.sqrt q * ‖v‖ := by
          exact mul_le_mul_of_nonneg_right
            (Q.boundaryTransfer_opNorm_le n t) (norm_nonneg v)
    have hsqrt : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
    have hsqrtSq : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq
    change (1 - q) * ‖v‖ ^ 2 ≤ ‖v‖ ^ 2 - ‖K v‖ ^ 2
    nlinarith [norm_nonneg v, norm_nonneg (K v)]

@[simp] theorem toApproximatingBoundaryL2PoincareGapCertificate_mass
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingExponentialBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    Q.toApproximatingBoundaryL2PoincareGapCertificate.mass = Q.mass :=
  rfl

/-- The generated Poincaré certificate has exactly the exponential defect. -/
@[simp] theorem toApproximatingBoundaryL2PoincareGapCertificate_defectFactor
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingExponentialBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (t : NNReal) :
    Q.toApproximatingBoundaryL2PoincareGapCertificate.defectFactor t =
      1 - Real.exp (-Q.mass * (t : ℝ)) :=
  rfl

/-- Exponential boundary transfer contraction generates the actual finite
periodic Wilson reflected-integral gap certificate. -/
noncomputable def toApproximatingFiniteIntegralGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingExponentialBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingFiniteIntegralGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.toApproximatingBoundaryL2PoincareGapCertificate
    |>.toApproximatingFiniteIntegralGapCertificate

/-- The same input generates completed vacuum norm decay with an explicitly
nonnegative factor. -/
noncomputable def toApproximatingNonnegativeVacuumGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingExponentialBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingNonnegativeVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.toApproximatingBoundaryL2PoincareGapCertificate
    |>.toApproximatingNonnegativeVacuumGapCertificate

@[simp] theorem toApproximatingFiniteIntegralGapCertificate_mass
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingExponentialBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    Q.toApproximatingFiniteIntegralGapCertificate.mass = Q.mass :=
  rfl

/-- Passing through completed nonnegative vacuum decay and back to finite
integrals recovers the exponential quadratic factor exactly. -/
@[simp] theorem nonnegativeVacuum_finiteIntegral_roundTrip_quadraticDecayFactor
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingExponentialBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (t : NNReal) :
    (PhysicalYangMillsEvenPeriodicWilsonOSApproximatingNonnegativeVacuumGapCertificate.toApproximatingFiniteIntegralGapCertificate
      Q.toApproximatingNonnegativeVacuumGapCertificate).quadraticDecayFactor t =
      Real.exp (-Q.mass * (t : ℝ)) := by
  simpa only [toApproximatingNonnegativeVacuumGapCertificate,
    toApproximatingBoundaryL2PoincareGapCertificate, sub_sub_cancel] using
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2PoincareGapCertificate.nonnegativeVacuum_finiteIntegral_roundTrip_quadraticDecayFactor
      Q.toApproximatingBoundaryL2PoincareGapCertificate t

end PhysicalYangMillsEvenPeriodicWilsonOSApproximatingExponentialBoundaryL2TransferGapCertificate

/-- Common-carrier continuum endpoint generated from exponential boundary
operator-norm contraction. -/
abbrev PhysicalYangMillsEvenPeriodicWilsonOSExponentialBoundaryL2TransferCommonCarrierGapTransfer
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (P : D.OSPreHilbertData)
    (T : P.StronglyContinuousPhysicalSemigroup)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant)
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingExponentialBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :=
  PhysicalYangMillsEvenPeriodicWilsonOSBoundaryL2PoincareCommonCarrierGapTransfer
    S D halfExtent N hN beta hbeta B hInvariant P T C
      Q.toApproximatingBoundaryL2PoincareGapCertificate

namespace PhysicalYangMillsEvenPeriodicWilsonOSExponentialBoundaryL2TransferCommonCarrierGapTransfer

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    {P : D.OSPreHilbertData}
    {T : P.StronglyContinuousPhysicalSemigroup}
    {C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingExponentialBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C}

noncomputable def finiteIntegralGapCertificate
    (_A : PhysicalYangMillsEvenPeriodicWilsonOSExponentialBoundaryL2TransferCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C Q) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingFiniteIntegralGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.toApproximatingFiniteIntegralGapCertificate

@[simp] theorem finiteIntegralGapCertificate_mass
    (A : PhysicalYangMillsEvenPeriodicWilsonOSExponentialBoundaryL2TransferCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C Q) :
    A.finiteIntegralGapCertificate.mass = Q.mass :=
  rfl

/-- Exponential boundary transfer contraction yields continuum
right-Hamiltonian coercivity with the same mass. -/
theorem rightHamiltonian_inner_ge_mass_mul_norm_sq
    (A : PhysicalYangMillsEvenPeriodicWilsonOSExponentialBoundaryL2TransferCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C Q)
    (psi : T.rightGeneratorDomain)
    (hpsi : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    Q.mass * ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
      inner ℝ (T.rightHamiltonian psi) (psi : P.PhysicalHilbert) := by
  exact
    PhysicalYangMillsEvenPeriodicWilsonOSBoundaryL2PoincareCommonCarrierGapTransfer.rightHamiltonian_inner_ge_mass_mul_norm_sq
      A psi hpsi

/-- The same lower bound survives graph closure. -/
theorem closedRightHamiltonian_inner_ge_mass_mul_norm_sq
    (A : PhysicalYangMillsEvenPeriodicWilsonOSExponentialBoundaryL2TransferCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C Q)
    (hP : P.IsNormalized)
    (psi : T.closedRightHamiltonian.domain)
    (hpsi : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    Q.mass * ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
      inner ℝ (T.closedRightHamiltonian psi)
        (psi : P.PhysicalHilbert) := by
  exact
    PhysicalYangMillsEvenPeriodicWilsonOSBoundaryL2PoincareCommonCarrierGapTransfer.closedRightHamiltonian_inner_ge_mass_mul_norm_sq
      A hP psi hpsi

/-- Zero energy is exactly the normalized continuum vacuum line. -/
theorem closedRightHamiltonian_eq_zero_iff_eq_inner_smul_vacuum
    (A : PhysicalYangMillsEvenPeriodicWilsonOSExponentialBoundaryL2TransferCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C Q)
    (hP : P.IsNormalized)
    (psi : T.closedRightHamiltonian.domain) :
    T.closedRightHamiltonian psi = 0 ↔
      (psi : P.PhysicalHilbert) =
        (inner ℝ (psi : P.PhysicalHilbert) P.vacuum) • P.vacuum := by
  exact
    PhysicalYangMillsEvenPeriodicWilsonOSBoundaryL2PoincareCommonCarrierGapTransfer.closedRightHamiltonian_eq_zero_iff_eq_inner_smul_vacuum
      A hP psi

end PhysicalYangMillsEvenPeriodicWilsonOSExponentialBoundaryL2TransferCommonCarrierGapTransfer

end MathlibAnalytic
end MGAP4D

end
