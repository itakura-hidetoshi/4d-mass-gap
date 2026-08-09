import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingBoundaryL2TransferGap
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRealizableDiscreteSemigroup
import MGAP4D.MathlibAnalytic.PhysicalYangMillsDerivedDiscreteTransferRate
import Mathlib.Tactic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

local instance realizableDerivedBoundaryTransferSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance realizableDerivedBoundaryTransferSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance realizableDerivedBoundaryTransferSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance realizableDerivedBoundaryTransferSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance realizableDerivedBoundaryTransferSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance realizableDerivedBoundaryTransferSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The actual realizable one-step Wilson boundary transfer, with no numerical
mass or decay rate built into the data.

The only structural content is membership of every Wilson boundary moment in
shared-boundary `L²`, one bounded operator `Kₙ` at each lattice scale, and the
exact intertwining of `Kₙ` with one genuine lattice-time step on centered OS
observables. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryL2TransferFamily
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S)
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)) where
  boundaryMoment_memLp :
    ∀ (n : ℕ)
      (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier),
      MemLp
        (fun b =>
          physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
            S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F b)
        2
        (periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N)
  boundaryTransfer :
    (n : ℕ) →
      PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N
  boundaryMoment_intertwining :
    ∀ (n : ℕ)
      (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier),
      let Pn :=
        physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
      boundaryTransfer n
          (physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2
            S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
            (Pn.vacuumCenteredCarrier F)
            (boundaryMoment_memLp n (Pn.vacuumCenteredCarrier F))) =
        physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
          (R.realizableCarrierTranslation hInvariant n 1
            (Pn.vacuumCenteredCarrier F))
          (boundaryMoment_memLp n
            (R.realizableCarrierTranslation hInvariant n 1
              (Pn.vacuumCenteredCarrier F)))

namespace PhysicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryL2TransferFamily

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta}
    {E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S}
    {R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}

/-- The one-step contraction factor is not postulated.  It is the operator norm
of the actual shared-boundary transfer itself. -/
def transferFactor
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryL2TransferFamily
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) : ℝ :=
  ‖A.boundaryTransfer n‖

@[simp] theorem transferFactor_eq_opNorm
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryL2TransferFamily
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    A.transferFactor n = ‖A.boundaryTransfer n‖ :=
  rfl

/-- The dynamically defined transfer factor is automatically nonnegative. -/
theorem transferFactor_nonneg
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryL2TransferFamily
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    0 ≤ A.transferFactor n :=
  norm_nonneg _

/-- Exact one-step intertwining and the Mathlib operator norm inequality give
one-step decay of the actual Wilson boundary moments with the factor
`rₙ = ‖Kₙ‖`. -/
theorem oneStep_centered_boundaryMomentL2_norm_le
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryL2TransferFamily
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
        (R.realizableCarrierTranslation hInvariant n 1
          (Pn.vacuumCenteredCarrier F))
        (A.boundaryMoment_memLp n
          (R.realizableCarrierTranslation hInvariant n 1
            (Pn.vacuumCenteredCarrier F)))‖ ≤
      A.transferFactor n *
        ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
          (Pn.vacuumCenteredCarrier F)
          (A.boundaryMoment_memLp n (Pn.vacuumCenteredCarrier F))‖ := by
  dsimp only
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  let F0 : Pn.Carrier := Pn.vacuumCenteredCarrier F
  let F1 : Pn.Carrier :=
    R.realizableCarrierTranslation hInvariant n 1 F0
  let v0 :=
    physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F0
      (A.boundaryMoment_memLp n F0)
  let v1 :=
    physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F1
      (A.boundaryMoment_memLp n F1)
  let K := A.boundaryTransfer n
  have hintertwining : K v0 = v1 := by
    simpa [Pn, F0, F1, v0, v1, K] using
      A.boundaryMoment_intertwining n F
  calc
    ‖v1‖ = ‖K v0‖ := by rw [← hintertwining]
    _ ≤ ‖K‖ * ‖v0‖ := K.le_opNorm v0
    _ = A.transferFactor n * ‖v0‖ := by rfl

/-- Squaring the preceding norm estimate gives the exact integrated
shared-boundary moment inequality with the dynamically defined factor. -/
theorem oneStep_centered_boundaryMoment_le
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryL2TransferFamily
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    (∫ b,
      ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
        (R.realizableCarrierTranslation hInvariant n 1
          (Pn.vacuumCenteredCarrier F)) b‖ ^ 2
      ∂(periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N)) ≤
      (A.transferFactor n) ^ 2 *
        ∫ b,
          ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
            S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
            (Pn.vacuumCenteredCarrier F) b‖ ^ 2
          ∂(periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N) := by
  dsimp only
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  let F0 : Pn.Carrier := Pn.vacuumCenteredCarrier F
  let F1 : Pn.Carrier :=
    R.realizableCarrierTranslation hInvariant n 1 F0
  let v0 :=
    physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F0
      (A.boundaryMoment_memLp n F0)
  let v1 :=
    physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F1
      (A.boundaryMoment_memLp n F1)
  have hnorm : ‖v1‖ ≤ A.transferFactor n * ‖v0‖ := by
    simpa [Pn, F0, F1, v0, v1] using
      A.oneStep_centered_boundaryMomentL2_norm_le n F
  have hsq :
      ‖v1‖ ^ 2 ≤ (A.transferFactor n) ^ 2 * ‖v0‖ ^ 2 := by
    nlinarith [norm_nonneg v1, norm_nonneg v0, A.transferFactor_nonneg n]
  rw [← physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2_norm_sq
    S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F1
    (A.boundaryMoment_memLp n F1)]
  rw [← physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2_norm_sq
    S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F0
    (A.boundaryMoment_memLp n F0)]
  exact hsq

end PhysicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryL2TransferFamily

/-- A factorization of the actual one-step boundary transfer through an
intermediate real normed feature space, with no quantitative mass assumption.
The resulting transfer operator is definitionally `synthesisₙ ∘ analysisₙ`. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryL2FactorizedTransferFamily
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S)
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)) where
  boundaryMoment_memLp :
    ∀ (n : ℕ)
      (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier),
      MemLp
        (fun b =>
          physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
            S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F b)
        2
        (periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N)
  FeatureState : ℕ → Type
  [featureNormedAddCommGroup : ∀ n, NormedAddCommGroup (FeatureState n)]
  [featureNormedSpace : ∀ n, NormedSpace ℝ (FeatureState n)]
  analysis :
    (n : ℕ) →
      PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N →L[ℝ]
        FeatureState n
  synthesis :
    (n : ℕ) → FeatureState n →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N
  boundaryMoment_factorized_intertwining :
    ∀ (n : ℕ)
      (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier),
      let Pn :=
        physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
      (synthesis n).comp (analysis n)
          (physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2
            S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
            (Pn.vacuumCenteredCarrier F)
            (boundaryMoment_memLp n (Pn.vacuumCenteredCarrier F))) =
        physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
          (R.realizableCarrierTranslation hInvariant n 1
            (Pn.vacuumCenteredCarrier F))
          (boundaryMoment_memLp n
            (R.realizableCarrierTranslation hInvariant n 1
              (Pn.vacuumCenteredCarrier F)))

attribute [instance]
  PhysicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryL2FactorizedTransferFamily.featureNormedAddCommGroup
  PhysicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryL2FactorizedTransferFamily.featureNormedSpace

namespace PhysicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryL2FactorizedTransferFamily

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta}
    {E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S}
    {R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}

/-- The actual boundary transfer generated by the factorization. -/
noncomputable def boundaryTransfer
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryL2FactorizedTransferFamily
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N :=
  (A.synthesis n).comp (A.analysis n)

/-- Forget the factorization while retaining the theorem-generated actual
boundary transfer family. -/
noncomputable def toBoundaryL2TransferFamily
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryL2FactorizedTransferFamily
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryL2TransferFamily
      S D halfExtent N hN beta hbeta Q E R hInvariant where
  boundaryMoment_memLp := A.boundaryMoment_memLp
  boundaryTransfer := A.boundaryTransfer
  boundaryMoment_intertwining := by
    intro n F
    exact A.boundaryMoment_factorized_intertwining n F

/-- Mathlib submultiplicativity bounds the dynamically defined transfer factor
by the product of the two actual factor norms. -/
theorem transferFactor_le_factorProduct
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryL2FactorizedTransferFamily
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    A.toBoundaryL2TransferFamily.transferFactor n ≤
      ‖A.synthesis n‖ * ‖A.analysis n‖ := by
  exact (A.synthesis n).opNorm_comp_le (A.analysis n)

end PhysicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryL2FactorizedTransferFamily

/-- A positive continuum mass rate extracted from the actual realizable Wilson
boundary transfer norms.

The numerical sequence is not an input: it is definitionally

`rₙ = ‖Kₙ‖`.

The remaining quantitative Yang--Mills content is precisely that these actual
operator norms satisfy `0 < rₙ ≤ 1` and that their logarithmic rates converge
to a positive limit. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryL2DerivedRateCertificate
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S)
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)) where
  transfer :
    PhysicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryL2TransferFamily
      S D halfExtent N hN beta hbeta Q E R hInvariant
  transferFactor_pos : ∀ n, 0 < transfer.transferFactor n
  transferFactor_le_one : ∀ n, transfer.transferFactor n ≤ 1
  mass : ℝ
  mass_pos : 0 < mass
  massRate_tendsto :
    Tendsto
      (fun n => -Real.log (transfer.transferFactor n) / S.latticeSpacing n)
      atTop (nhds mass)

namespace PhysicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryL2DerivedRateCertificate

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta}
    {E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S}
    {R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}

/-- Package the actual Wilson boundary-transfer norm sequence into the generic
positive discrete transfer-rate limit of #1502. -/
noncomputable def toPositiveDiscreteTransferRateLimit
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryL2DerivedRateCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    PositiveDiscreteTransferRateLimit
      S.latticeSpacing A.transfer.transferFactor where
  latticeSpacing_pos := S.latticeSpacing_pos
  latticeSpacing_tendsto_zero := S.latticeSpacing_tendsto_zero
  transferFactor_pos := A.transferFactor_pos
  transferFactor_le_one := A.transferFactor_le_one
  mass := A.mass
  mass_pos := A.mass_pos
  massRate_tendsto := A.massRate_tendsto

/-- The finite mass rate is therefore literally the logarithmic rate of the
actual Wilson boundary-transfer operator norm. -/
def massRate
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryL2DerivedRateCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) : ℝ :=
  -Real.log (A.transfer.transferFactor n) / S.latticeSpacing n

@[simp] theorem massRate_eq
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryL2DerivedRateCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    A.massRate n =
      -Real.log ‖A.transfer.boundaryTransfer n‖ / S.latticeSpacing n := by
  rfl

/-- The derived finite rates converge to the certificate's continuum mass. -/
theorem massRate_tendsto_mass
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryL2DerivedRateCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    Tendsto A.massRate atTop (nhds A.mass) := by
  simpa only [massRate] using A.massRate_tendsto

/-- At every scale the actual boundary-transfer norm is exactly the exponential
of its own derived mass rate times the physical lattice spacing. -/
theorem transferFactor_eq_exp_neg_massRate_mul_spacing
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryL2DerivedRateCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    A.transfer.transferFactor n =
      Real.exp (-A.massRate n * S.latticeSpacing n) := by
  exact A.toPositiveDiscreteTransferRateLimit.factor_eq_exp_neg_massRate_mul_spacing n

/-- For every fixed physical time, the genuinely discrete floor-selected
geometric power of the actual Wilson transfer norm converges to the continuum
exponential with the mass derived from those norms. -/
theorem floorPow_tendsto
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryL2DerivedRateCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (t : NNReal) :
    Tendsto
      (fun n =>
        (A.transfer.transferFactor n) ^
          physicalTemporalFloorNatStep S.latticeSpacing t n)
      atTop
      (nhds (Real.exp (-A.mass * (t : ℝ)))) := by
  exact A.toPositiveDiscreteTransferRateLimit.floorPow_tendsto t

/-- The corresponding half-time squared factor has the full-time continuum
quadratic limit. -/
theorem floorHalfQuadraticFactor_tendsto
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryL2DerivedRateCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (t : NNReal) :
    Tendsto
      (fun n =>
        (A.toPositiveDiscreteTransferRateLimit.floorFactor (t / 2) n) ^ 2)
      atTop
      (nhds (Real.exp (-A.mass * (t : ℝ)))) := by
  exact A.toPositiveDiscreteTransferRateLimit.floorHalfQuadraticFactor_tendsto t

end PhysicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryL2DerivedRateCertificate

end MathlibAnalytic
end MGAP4D

end