import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonDobrushinCoefficientBoundL2
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingDobrushinGibbsBoundaryL2TransferGap

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

/-- A volume-uniform finite Wilson package combining the genuine compact Gibbs
Dobrushin matrix layer with an explicit shared-boundary transfer
factorization.

For every selected scale `n`, the data contain the actual periodic `SU(N)`
Wilson Gibbs `L²` carrier and a genuine compact-Haar Dobrushin
matrix/random-scan certificate.  The scale-wise coefficients may vary, but are
bounded by one strict common coefficient `coefficientBound < 1`.

The actual shared-boundary transfer is represented as

`boundarySynthesis n t ∘ gibbsEvolution n t ∘ boundaryAnalysis n t`.

Instead of assuming the norm of this three-factor composition directly, the
package asks separately for

* contractive boundary analysis;
* exponential Gibbs evolution contraction at the common Dobrushin rate;
* contractive boundary synthesis.

Their product estimate is proved below.  The exact OS boundary-moment
intertwining then feeds the completed finite-integral, vacuum-decay, continuum
coercivity, graph-closure, and normalized-vacuum kernel route.

The compact Gibbs evolution and Euclidean-time OS translation remain distinct
operators on distinct Hilbert spaces. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSApproximatingUniformDobrushinGibbsBoundaryL2TransferGapCertificate
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
  coefficientBound : ℝ
  coefficientBound_nonneg : 0 ≤ coefficientBound
  coefficientBound_lt_one : coefficientBound < 1
  dobrushinMatrix : ∀ n,
    ContinuousCompactOrientedGaugeWilsonDobrushinMatrixRandomScanCertificate
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength (halfExtent n))
        N hN (beta n) (hbeta n))
  coefficient_le_bound :
    ∀ n, (dobrushinMatrix n).coefficient ≤ coefficientBound
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
  boundaryAnalysis :
    (n : ℕ) → (t : NNReal) →
      PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryGibbsL2
          (halfExtent n) N hN (beta n) (hbeta n)
  gibbsEvolution :
    (n : ℕ) → (t : NNReal) →
      PeriodicHypercubicEvenSpecialUnitaryGibbsL2
          (halfExtent n) N hN (beta n) (hbeta n) →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryGibbsL2
          (halfExtent n) N hN (beta n) (hbeta n)
  boundarySynthesis :
    (n : ℕ) → (t : NNReal) →
      PeriodicHypercubicEvenSpecialUnitaryGibbsL2
          (halfExtent n) N hN (beta n) (hbeta n) →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N
  boundaryAnalysis_opNorm_le_one :
    ∀ n t, ‖boundaryAnalysis n t‖ ≤ 1
  gibbsEvolution_opNorm_le :
    ∀ n t,
      ‖gibbsEvolution n t‖ ≤
        Real.sqrt
          (Real.exp
            (-continuousCompactOrientedDobrushinHeatBathGap coefficientBound *
              (t : ℝ)))
  boundarySynthesis_opNorm_le_one :
    ∀ n t, ‖boundarySynthesis n t‖ ≤ 1
  boundaryMoment_intertwining :
    ∀ (n : ℕ) (t : NNReal),
      let Pn :=
        physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta B hInvariant n
      let Tn := C.toPositiveTimeObservableContractionSemigroup n
      ∀ F : Pn.Carrier,
        (boundarySynthesis n t).comp
            ((gibbsEvolution n t).comp (boundaryAnalysis n t))
            (physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2
              S D halfExtent N hN beta hbeta B hInvariant n
              (Pn.vacuumCenteredCarrier F)
              (boundaryMoment_memLp n (Pn.vacuumCenteredCarrier F))) =
          physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2
            S D halfExtent N hN beta hbeta B hInvariant n
            (Tn.carrierTranslation (t / 2) (Pn.vacuumCenteredCarrier F))
            (boundaryMoment_memLp n
              (Tn.carrierTranslation (t / 2) (Pn.vacuumCenteredCarrier F)))

namespace PhysicalYangMillsEvenPeriodicWilsonOSApproximatingUniformDobrushinGibbsBoundaryL2TransferGapCertificate

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

/-- The common coefficient bound gives a positive scale-independent rate. -/
theorem uniformGap_pos
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingUniformDobrushinGibbsBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    0 < continuousCompactOrientedDobrushinHeatBathGap Q.coefficientBound := by
  unfold continuousCompactOrientedDobrushinHeatBathGap
  exact sub_pos.mpr Q.coefficientBound_lt_one

/-- Every actual finite Wilson Gibbs system satisfies the heat-bath Poincaré
inequality with the same common gap. -/
theorem gibbsHeatBathPoincareL2
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingUniformDobrushinGibbsBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (n : ℕ) :
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength (halfExtent n))
      N hN (beta n) (hbeta n)).HeatBathPoincareL2
        (continuousCompactOrientedDobrushinHeatBathGap Q.coefficientBound) :=
  continuous_compact_oriented_dobrushinCoefficientBoundHeatBathPoincareL2
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength (halfExtent n))
      N hN (beta n) (hbeta n))
    (Q.dobrushinMatrix n)
    Q.coefficientBound Q.coefficientBound_nonneg Q.coefficientBound_lt_one
    (Q.coefficient_le_bound n)

/-- The same common rate controls every finite Gibbs heat-bath Hamiltonian on
the Gibbs-vacuum orthogonal sector. -/
theorem gibbsHeatBathHamiltonian_coercive
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingUniformDobrushinGibbsBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (n : ℕ)
    (f : PeriodicHypercubicEvenSpecialUnitaryGibbsL2
      (halfExtent n) N hN (beta n) (hbeta n))
    (hf : inner ℝ
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength (halfExtent n))
        N hN (beta n) (hbeta n)).gibbsVacuumL2 f = 0) :
    continuousCompactOrientedDobrushinHeatBathGap Q.coefficientBound *
        ‖f‖ ^ 2 ≤
      inner ℝ
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength (halfExtent n))
          N hN (beta n) (hbeta n)).heatBathHamiltonianL2 f) f :=
  continuous_compact_oriented_dobrushinCoefficientBoundHamiltonianL2_gap_on_vacuumOrthogonal
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength (halfExtent n))
      N hN (beta n) (hbeta n))
    (Q.dobrushinMatrix n)
    Q.coefficientBound Q.coefficientBound_nonneg Q.coefficientBound_lt_one
    (Q.coefficient_le_bound n) f hf

/-- At every finite scale, the Gibbs heat-bath Hamiltonian has exactly the
normalized Gibbs-vacuum line as kernel. -/
theorem gibbsHeatBathHamiltonian_eq_zero_iff_eq_inner_smul_vacuum
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingUniformDobrushinGibbsBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (n : ℕ)
    (f : PeriodicHypercubicEvenSpecialUnitaryGibbsL2
      (halfExtent n) N hN (beta n) (hbeta n)) :
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength (halfExtent n))
      N hN (beta n) (hbeta n)).heatBathHamiltonianL2 f = 0 ↔
      f = inner ℝ
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength (halfExtent n))
          N hN (beta n) (hbeta n)).gibbsVacuumL2 f •
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength (halfExtent n))
          N hN (beta n) (hbeta n)).gibbsVacuumL2 :=
  continuous_compact_oriented_dobrushinCoefficientBoundHamiltonianL2_eq_zero_iff_eq_inner_smul_vacuum
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength (halfExtent n))
      N hN (beta n) (hbeta n))
    (Q.dobrushinMatrix n)
    Q.coefficientBound Q.coefficientBound_nonneg Q.coefficientBound_lt_one
    (Q.coefficient_le_bound n) f

/-- Contractive analysis and synthesis together with Gibbs evolution
contraction imply the full three-factor boundary-transfer norm estimate. -/
theorem factor_opNorm_mul_le
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingUniformDobrushinGibbsBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (n : ℕ)
    (t : NNReal) :
    ‖Q.boundarySynthesis n t‖ *
        (‖Q.gibbsEvolution n t‖ * ‖Q.boundaryAnalysis n t‖) ≤
      Real.sqrt
        (Real.exp
          (-continuousCompactOrientedDobrushinHeatBathGap Q.coefficientBound *
            (t : ℝ))) := by
  calc
    ‖Q.boundarySynthesis n t‖ *
        (‖Q.gibbsEvolution n t‖ * ‖Q.boundaryAnalysis n t‖) ≤
      1 * (‖Q.gibbsEvolution n t‖ * ‖Q.boundaryAnalysis n t‖) :=
        mul_le_mul_of_nonneg_right
          (Q.boundarySynthesis_opNorm_le_one n t)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = ‖Q.gibbsEvolution n t‖ * ‖Q.boundaryAnalysis n t‖ := by
      rw [one_mul]
    _ ≤ Real.sqrt
          (Real.exp
            (-continuousCompactOrientedDobrushinHeatBathGap Q.coefficientBound *
              (t : ℝ))) * ‖Q.boundaryAnalysis n t‖ :=
        mul_le_mul_of_nonneg_right
          (Q.gibbsEvolution_opNorm_le n t) (norm_nonneg _)
    _ ≤ Real.sqrt
          (Real.exp
            (-continuousCompactOrientedDobrushinHeatBathGap Q.coefficientBound *
              (t : ℝ))) * 1 :=
        mul_le_mul_of_nonneg_left
          (Q.boundaryAnalysis_opNorm_le_one n t) (Real.sqrt_nonneg _)
    _ = Real.sqrt
          (Real.exp
            (-continuousCompactOrientedDobrushinHeatBathGap Q.coefficientBound *
              (t : ℝ))) := by
      rw [mul_one]

/-- Assemble the scale-wise matrix certificates and separate factor norms into
the typed Gibbs/shared-boundary transfer certificate of the previous layer. -/
noncomputable def toApproximatingDobrushinGibbsBoundaryL2TransferGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingUniformDobrushinGibbsBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingDobrushinGibbsBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C where
  coefficient := Q.coefficientBound
  coefficient_nonneg := Q.coefficientBound_nonneg
  coefficient_lt_one := Q.coefficientBound_lt_one
  dobrushinRayleigh := fun n =>
    (Q.dobrushinMatrix n).toCoefficientBoundRayleighCertificate
      Q.coefficientBound Q.coefficientBound_nonneg Q.coefficientBound_lt_one
      (Q.coefficient_le_bound n)
  dobrushinRayleigh_coefficient := fun _ => rfl
  exchange := Q.exchange
  gram_integrable := Q.gram_integrable
  boundaryMoment_memLp := Q.boundaryMoment_memLp
  boundaryAnalysis := Q.boundaryAnalysis
  gibbsEvolution := Q.gibbsEvolution
  boundarySynthesis := Q.boundarySynthesis
  boundaryMoment_intertwining := Q.boundaryMoment_intertwining
  factor_opNorm_mul_le := Q.factor_opNorm_mul_le

/-- The integrated package generates the exponential actual shared-boundary
transfer certificate with mass `1 - coefficientBound`. -/
noncomputable def toApproximatingExponentialBoundaryL2TransferGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingUniformDobrushinGibbsBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingExponentialBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.toApproximatingDobrushinGibbsBoundaryL2TransferGapCertificate
    |>.toApproximatingExponentialBoundaryL2TransferGapCertificate

/-- The same data generate the Dobrushin-rate wrapper used by the complete
finite and continuum route. -/
noncomputable def toApproximatingDobrushinRateBoundaryL2TransferGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingUniformDobrushinGibbsBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingDobrushinRateBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.toApproximatingDobrushinGibbsBoundaryL2TransferGapCertificate
    |>.toApproximatingDobrushinRateBoundaryL2TransferGapCertificate

/-- The actual finite periodic Wilson reflected-integral gap follows with the
unchanged common mass. -/
noncomputable def toApproximatingFiniteIntegralGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingUniformDobrushinGibbsBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingFiniteIntegralGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.toApproximatingDobrushinRateBoundaryL2TransferGapCertificate
    |>.toApproximatingFiniteIntegralGapCertificate

/-- Completed nonnegative vacuum norm decay follows from the same package. -/
noncomputable def toApproximatingNonnegativeVacuumGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingUniformDobrushinGibbsBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingNonnegativeVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.toApproximatingDobrushinRateBoundaryL2TransferGapCertificate
    |>.toApproximatingNonnegativeVacuumGapCertificate

@[simp] theorem toApproximatingFiniteIntegralGapCertificate_mass
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingUniformDobrushinGibbsBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    Q.toApproximatingFiniteIntegralGapCertificate.mass =
      continuousCompactOrientedDobrushinHeatBathGap Q.coefficientBound :=
  rfl

@[simp] theorem nonnegativeVacuum_finiteIntegral_roundTrip_quadraticDecayFactor
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingUniformDobrushinGibbsBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (t : NNReal) :
    (PhysicalYangMillsEvenPeriodicWilsonOSApproximatingNonnegativeVacuumGapCertificate.toApproximatingFiniteIntegralGapCertificate
      Q.toApproximatingNonnegativeVacuumGapCertificate).quadraticDecayFactor t =
      Real.exp
        (-continuousCompactOrientedDobrushinHeatBathGap Q.coefficientBound *
          (t : ℝ)) := by
  exact
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingDobrushinRateBoundaryL2TransferGapCertificate.nonnegativeVacuum_finiteIntegral_roundTrip_quadraticDecayFactor
      Q.toApproximatingDobrushinRateBoundaryL2TransferGapCertificate t

end PhysicalYangMillsEvenPeriodicWilsonOSApproximatingUniformDobrushinGibbsBoundaryL2TransferGapCertificate

/-- Common-carrier continuum endpoint generated by the complete uniform
Dobrushin Gibbs/shared-boundary transfer package. -/
abbrev PhysicalYangMillsEvenPeriodicWilsonOSUniformDobrushinGibbsBoundaryL2TransferCommonCarrierGapTransfer
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
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingUniformDobrushinGibbsBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :=
  PhysicalYangMillsEvenPeriodicWilsonOSDobrushinRateBoundaryL2TransferCommonCarrierGapTransfer
    S D halfExtent N hN beta hbeta B hInvariant P T C
      Q.toApproximatingDobrushinRateBoundaryL2TransferGapCertificate

namespace PhysicalYangMillsEvenPeriodicWilsonOSUniformDobrushinGibbsBoundaryL2TransferCommonCarrierGapTransfer

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
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingUniformDobrushinGibbsBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C}

noncomputable def finiteIntegralGapCertificate
    (_A : PhysicalYangMillsEvenPeriodicWilsonOSUniformDobrushinGibbsBoundaryL2TransferCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C Q) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingFiniteIntegralGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.toApproximatingFiniteIntegralGapCertificate

@[simp] theorem finiteIntegralGapCertificate_mass
    (A : PhysicalYangMillsEvenPeriodicWilsonOSUniformDobrushinGibbsBoundaryL2TransferCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C Q) :
    A.finiteIntegralGapCertificate.mass =
      continuousCompactOrientedDobrushinHeatBathGap Q.coefficientBound :=
  rfl

/-- Continuum right-Hamiltonian coercivity has exactly the common uniform
Dobrushin rate. -/
theorem rightHamiltonian_inner_ge_uniformGap_mul_norm_sq
    (A : PhysicalYangMillsEvenPeriodicWilsonOSUniformDobrushinGibbsBoundaryL2TransferCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C Q)
    (psi : T.rightGeneratorDomain)
    (hpsi : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    continuousCompactOrientedDobrushinHeatBathGap Q.coefficientBound *
        ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
      inner ℝ (T.rightHamiltonian psi) (psi : P.PhysicalHilbert) :=
  PhysicalYangMillsEvenPeriodicWilsonOSDobrushinRateBoundaryL2TransferCommonCarrierGapTransfer.rightHamiltonian_inner_ge_dobrushinGap_mul_norm_sq
    A psi hpsi

/-- The same common lower bound survives graph closure. -/
theorem closedRightHamiltonian_inner_ge_uniformGap_mul_norm_sq
    (A : PhysicalYangMillsEvenPeriodicWilsonOSUniformDobrushinGibbsBoundaryL2TransferCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C Q)
    (hP : P.IsNormalized)
    (psi : T.closedRightHamiltonian.domain)
    (hpsi : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    continuousCompactOrientedDobrushinHeatBathGap Q.coefficientBound *
        ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
      inner ℝ (T.closedRightHamiltonian psi)
        (psi : P.PhysicalHilbert) :=
  PhysicalYangMillsEvenPeriodicWilsonOSDobrushinRateBoundaryL2TransferCommonCarrierGapTransfer.closedRightHamiltonian_inner_ge_dobrushinGap_mul_norm_sq
    A hP psi hpsi

/-- The graph-closed continuum Hamiltonian has exactly the normalized vacuum
line as its zero-energy space. -/
theorem closedRightHamiltonian_eq_zero_iff_eq_inner_smul_vacuum
    (A : PhysicalYangMillsEvenPeriodicWilsonOSUniformDobrushinGibbsBoundaryL2TransferCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C Q)
    (hP : P.IsNormalized)
    (psi : T.closedRightHamiltonian.domain) :
    T.closedRightHamiltonian psi = 0 ↔
      (psi : P.PhysicalHilbert) =
        (inner ℝ (psi : P.PhysicalHilbert) P.vacuum) • P.vacuum :=
  PhysicalYangMillsEvenPeriodicWilsonOSDobrushinRateBoundaryL2TransferCommonCarrierGapTransfer.closedRightHamiltonian_eq_zero_iff_eq_inner_smul_vacuum
    A hP psi

end PhysicalYangMillsEvenPeriodicWilsonOSUniformDobrushinGibbsBoundaryL2TransferCommonCarrierGapTransfer

end MathlibAnalytic
end MGAP4D

end
