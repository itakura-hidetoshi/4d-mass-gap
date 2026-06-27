import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingBoundaryMomentGap
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

local instance (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The real `L²` Hilbert space of shared-boundary functions for one finite
periodic Wilson lattice. -/
abbrev PeriodicHypercubicEvenSpecialUnitaryBoundaryL2
    (H N : ℕ) : Type :=
  MeasureTheory.Lp ℝ 2
    (periodicHypercubicEvenBoundaryHaarMeasure H N)

/-- Regard one actual Wilson OS boundary-moment function as a vector in the
shared-boundary `L²` Hilbert space. -/
noncomputable def physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2
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
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier)
    (hF : MemLp
      (fun b =>
        physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
          S D halfExtent N hN beta hbeta B hInvariant n F b)
      2
      (periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N)) :
    PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N :=
  hF.toLp fun b =>
    physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
      S D halfExtent N hN beta hbeta B hInvariant n F b

/-- The squared `L²` norm of a boundary-moment vector is exactly the boundary
Haar integral used in the finite Wilson OS quadratic form. -/
theorem physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2_norm_sq
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
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier)
    (hF : MemLp
      (fun b =>
        physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
          S D halfExtent N hN beta hbeta B hInvariant n F b)
      2
      (periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N)) :
    ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2
        S D halfExtent N hN beta hbeta B hInvariant n F hF‖ ^ 2 =
      ∫ b,
        ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
          S D halfExtent N hN beta hbeta B hInvariant n F b‖ ^ 2
        ∂(periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N) := by
  let v :=
    physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2
      S D halfExtent N hN beta hbeta B hInvariant n F hF
  calc
    ‖v‖ ^ 2 = inner ℝ v v := by
      simpa using (real_inner_self_eq_norm_sq v).symm
    _ = ∫ b, inner ℝ (v b) (v b)
        ∂(periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N) :=
      MeasureTheory.L2.inner_def v v
    _ = ∫ b,
        ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
          S D halfExtent N hN beta hbeta B hInvariant n F b‖ ^ 2
        ∂(periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N) := by
      apply integral_congr_ae
      filter_upwards [hF.coeFn_toLp] with b hb
      rw [show v b =
          physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
            S D halfExtent N hN beta hbeta B hInvariant n F b by
        exact hb]
      exact real_inner_self_eq_norm_sq _

/-- A scale-uniform finite Wilson OS gap certificate expressed as a contraction
of an actual transfer operator on the shared-boundary `L²` Hilbert space.

The intertwining field identifies observable half-time translation with the
boundary transfer operator acting on boundary Gram moments.  Its operator norm
bound then generates the integrated boundary-moment decay used by the complete
continuum Hamiltonian route. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2TransferGapCertificate
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
  quadraticDecayFactor : NNReal → ℝ
  quadraticDecayFactor_nonneg : ∀ t, 0 ≤ quadraticDecayFactor t
  slope_tendsto :
    Tendsto
      (fun t : NNReal =>
        (t : ℝ)⁻¹ *
          (1 - Real.sqrt (quadraticDecayFactor (t + t))))
      (nhdsWithin 0 (Ioi 0))
      (nhds mass)
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
      ‖boundaryTransfer n t‖ ≤ Real.sqrt (quadraticDecayFactor t)

namespace PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2TransferGapCertificate

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

/-- Boundary `L²` transfer-operator contraction generates the integrated
boundary-moment gap certificate. -/
noncomputable def toApproximatingBoundaryMomentGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryMomentGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C where
  mass := Q.mass
  mass_pos := Q.mass_pos
  quadraticDecayFactor := Q.quadraticDecayFactor
  quadraticDecayFactor_nonneg := Q.quadraticDecayFactor_nonneg
  slope_tendsto := Q.slope_tendsto
  exchange := Q.exchange
  gram_integrable := Q.gram_integrable
  finite_boundary_moment_decay := by
    intro n t
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n
    let Tn := C.toPositiveTimeObservableContractionSemigroup n
    intro F
    let F0 : Pn.Carrier := Pn.vacuumCenteredCarrier F
    let Ft : Pn.Carrier := Tn.carrierTranslation (t / 2) F0
    let v0 :=
      physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2
        S D halfExtent N hN beta hbeta B hInvariant n F0
        (Q.boundaryMoment_memLp n F0)
    let vt :=
      physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2
        S D halfExtent N hN beta hbeta B hInvariant n Ft
        (Q.boundaryMoment_memLp n Ft)
    let K := Q.boundaryTransfer n t
    have hintertwining : K v0 = vt := by
      simpa [F0, Ft, v0, vt, K, Pn, Tn] using
        Q.boundaryMoment_intertwining n t F
    have hnorm :
        ‖vt‖ ≤ Real.sqrt (Q.quadraticDecayFactor t) * ‖v0‖ := by
      calc
        ‖vt‖ = ‖K v0‖ := by rw [← hintertwining]
        _ ≤ ‖K‖ * ‖v0‖ := K.le_opNorm v0
        _ ≤ Real.sqrt (Q.quadraticDecayFactor t) * ‖v0‖ :=
          mul_le_mul_of_nonneg_right
            (Q.boundaryTransfer_opNorm_le n t) (norm_nonneg v0)
    have hsq :
        ‖vt‖ ^ 2 ≤ Q.quadraticDecayFactor t * ‖v0‖ ^ 2 := by
      have hq : 0 ≤ Q.quadraticDecayFactor t :=
        Q.quadraticDecayFactor_nonneg t
      have hsqrt : 0 ≤ Real.sqrt (Q.quadraticDecayFactor t) :=
        Real.sqrt_nonneg _
      have hsqrtSq :
          (Real.sqrt (Q.quadraticDecayFactor t)) ^ 2 =
            Q.quadraticDecayFactor t :=
        Real.sq_sqrt hq
      nlinarith [norm_nonneg vt, norm_nonneg v0]
    rw [← physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2_norm_sq
      S D halfExtent N hN beta hbeta B hInvariant n Ft
      (Q.boundaryMoment_memLp n Ft)]
    rw [← physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2_norm_sq
      S D halfExtent N hN beta hbeta B hInvariant n F0
      (Q.boundaryMoment_memLp n F0)]
    exact hsq

/-- A shared-boundary `L²` transfer-operator gap therefore generates the full
finite Wilson OS norm-decay certificate used by the continuum mass-gap route. -/
noncomputable def toApproximatingVacuumGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.toApproximatingBoundaryMomentGapCertificate
    |>.toApproximatingVacuumGapCertificate

end PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2TransferGapCertificate

end MathlibAnalytic
end MGAP4D

end
