import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSTimeAverageHamiltonianCore
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCommonCarrierFiniteWilsonCoreHamiltonianStrongLimit
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace LinearPMap

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- Finite Wilson selected eigenvectors smoothed by shrinking positive-time
averages in the continuum common carrier.

Time averaging puts every embedded vector in the canonical right-Hamiltonian
core.  The only operator compatibility input is therefore the semigroup
finite-difference quotient, rather than prior membership in the generator or
closed-Hamiltonian domain. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonTimeAverageApproximateEigenpairStrongLimitData
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
    {T : P.StronglyContinuousPhysicalSemigroup}
    {C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C}
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C Q)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (F : FiniteWilsonOSAutomaticExactGapFiniteDimensionalHamiltonianContractionData W)
    [DecidableEq A.toVacuumSemigroupGapSlope.BelowHalfMassShift]
    (nodes : Finset A.toVacuumSemigroupGapSlope.BelowHalfMassShift)
    (orderCap : ℕ) where
  realization :
    PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonExcitationRealizationData
      A F
  finiteWitness :
    (n : ℕ) →
      FiniteWilsonFiniteDimensionalHamiltonianConfluentSpectralWitnessData
        F n
          (fun sigma : A.toVacuumSemigroupGapSlope.BelowHalfMassShift => sigma.1)
          nodes orderCap
  SpectralIndex : Type
  [spectralFintype : Fintype SpectralIndex]
  finiteIndexEquiv :
    ∀ n, SpectralIndex ≃ (finiteWitness n).SpectralIndex
  width : ℕ → NNReal
  width_pos : ∀ n, 0 < width n
  width_tendsto_zero :
    Tendsto width atTop (nhdsWithin 0 (Ioi 0))
  spectralValue : SpectralIndex → ℝ
  spectralValue_injective : Function.Injective spectralValue
  spectralVector : SpectralIndex → P.VacuumOrthogonalHilbert
  approximateValue_tendsto :
    ∀ k,
      Tendsto
        (fun n => (finiteWitness n).spectralValue (finiteIndexEquiv n k))
        atTop (nhds (spectralValue k))
  embeddedVector_tendsto :
    ∀ k,
      Tendsto
        (fun n =>
          realization.excitationEmbed n
            ((finiteWitness n).spectralVector (finiteIndexEquiv n k)))
        atTop (nhds (spectralVector k))
  semigroupDifferenceQuotientCompatibility_tendsto_zero :
    ∀ k,
      Tendsto
        (fun n =>
          T.rightHamiltonianDifferenceQuotient
              (((realization.excitationEmbed n
                    ((finiteWitness n).spectralVector
                      (finiteIndexEquiv n k)) :
                  P.VacuumOrthogonalHilbert) : P.PhysicalHilbert))
              (width n) -
            (((realization.excitationEmbed n
                  (F.hamiltonian n
                    ((finiteWitness n).spectralVector
                      (finiteIndexEquiv n k))) :
                P.VacuumOrthogonalHilbert) : P.PhysicalHilbert)))
        atTop (nhds 0)

attribute [instance]
  PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonTimeAverageApproximateEigenpairStrongLimitData.spectralFintype

namespace PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonTimeAverageApproximateEigenpairStrongLimitData

variable
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
    {T : P.StronglyContinuousPhysicalSemigroup}
    {C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C}
    {A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C Q}
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {hSelf : IsSelfAdjoint T.closedRightHamiltonian}
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {F : FiniteWilsonOSAutomaticExactGapFiniteDimensionalHamiltonianContractionData W}
    [DecidableEq A.toVacuumSemigroupGapSlope.BelowHalfMassShift]
    {nodes : Finset A.toVacuumSemigroupGapSlope.BelowHalfMassShift}
    {orderCap : ℕ}

/-- The selected finite Wilson energy tracked by the common spectral index. -/
def approximateValue
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonTimeAverageApproximateEigenpairStrongLimitData
      A hInnerSymmetric hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) : ℝ :=
  (R.finiteWitness n).spectralValue (R.finiteIndexEquiv n k)

/-- The selected finite Wilson eigenvector tracked by the common spectral index. -/
def finiteVector
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonTimeAverageApproximateEigenpairStrongLimitData
      A hInnerSymmetric hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) : F.StateSpace :=
  (R.finiteWitness n).spectralVector (R.finiteIndexEquiv n k)

/-- The selected finite vector embedded in the continuum excitation carrier. -/
noncomputable def embeddedVector
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonTimeAverageApproximateEigenpairStrongLimitData
      A hInnerSymmetric hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) : P.VacuumOrthogonalHilbert :=
  R.realization.excitationEmbed n (R.finiteVector n k)

/-- The embedded selected vector in the ambient physical Hilbert space. -/
noncomputable def ambientEmbeddedVector
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonTimeAverageApproximateEigenpairStrongLimitData
      A hInnerSymmetric hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) : P.PhysicalHilbert :=
  ((R.embeddedVector n k : P.VacuumOrthogonalHilbert) : P.PhysicalHilbert)

/-- The shrinking time average bundled in the canonical right-Hamiltonian core. -/
noncomputable def timeAveragedCoreVector
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonTimeAverageApproximateEigenpairStrongLimitData
      A hInnerSymmetric hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) : T.rightHamiltonianLinearPMap.domain :=
  T.timeAverageRightHamiltonianDomain
    (R.width n) (R.ambientEmbeddedVector n k)

/-- Symmetry keeps every time-averaged selected vector in the continuum
excitation sector. -/
theorem timeAverage_mem_vacuumOrthogonal
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonTimeAverageApproximateEigenpairStrongLimitData
      A hInnerSymmetric hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) :
    T.timeAverage (R.width n) (R.ambientEmbeddedVector n k) ∈
      P.vacuumOrthogonal :=
  T.timeAverage_mem_vacuumOrthogonal hInnerSymmetric (R.width n)
    (R.embeddedVector n k).property

/-- The shrinking time average as a vector in the complete excitation Hilbert
space. -/
noncomputable def timeAveragedVector
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonTimeAverageApproximateEigenpairStrongLimitData
      A hInnerSymmetric hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) : P.VacuumOrthogonalHilbert :=
  ⟨T.timeAverage (R.width n) (R.ambientEmbeddedVector n k),
    R.timeAverage_mem_vacuumOrthogonal n k⟩

/-- The time-averaged core vector lifted automatically to the graph-closed
ambient Hamiltonian domain. -/
noncomputable def closedAmbientVector
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonTimeAverageApproximateEigenpairStrongLimitData
      A hInnerSymmetric hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) : T.closedRightHamiltonian.domain :=
  LinearPMap.domainPointOfLE
    T.rightHamiltonianLinearPMap_le_closedRightHamiltonian
    (R.timeAveragedCoreVector n k)

/-- The automatically smoothed and lifted approximation in the domain of the
closed excitation Hamiltonian. -/
noncomputable def approximateVector
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonTimeAverageApproximateEigenpairStrongLimitData
      A hInnerSymmetric hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) :
    (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf).domain := by
  refine ⟨R.timeAveragedVector n k, ?_⟩
  change T.timeAverage (R.width n) (R.ambientEmbeddedVector n k) ∈
    T.closedRightHamiltonian.domain
  exact T.rightHamiltonianLinearPMap_le_closedRightHamiltonian.1
    (R.timeAveragedCoreVector n k).property

@[simp] theorem approximateVector_coe
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonTimeAverageApproximateEigenpairStrongLimitData
      A hInnerSymmetric hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) :
    (R.approximateVector n k : P.VacuumOrthogonalHilbert) =
      R.timeAveragedVector n k :=
  rfl

/-- The semigroup finite-difference quotient remains vacuum orthogonal. -/
theorem differenceQuotient_mem_vacuumOrthogonal
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonTimeAverageApproximateEigenpairStrongLimitData
      A hInnerSymmetric hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) :
    T.rightHamiltonianDifferenceQuotient
        (R.ambientEmbeddedVector n k) (R.width n) ∈
      P.vacuumOrthogonal := by
  unfold rightHamiltonianDifferenceQuotient
  apply P.vacuumOrthogonal.smul_mem
  apply P.vacuumOrthogonal.sub_mem
  · exact (R.embeddedVector n k).property
  · exact T.toPhysicalSemigroup.operator_mem_vacuumOrthogonal
      hInnerSymmetric (R.width n) (R.ambientEmbeddedVector n k)
      (R.embeddedVector n k).property

/-- The semigroup finite-difference quotient as an excitation vector. -/
noncomputable def differenceQuotientValue
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonTimeAverageApproximateEigenpairStrongLimitData
      A hInnerSymmetric hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) : P.VacuumOrthogonalHilbert :=
  ⟨T.rightHamiltonianDifferenceQuotient
      (R.ambientEmbeddedVector n k) (R.width n),
    R.differenceQuotient_mem_vacuumOrthogonal n k⟩

/-- The restricted closed Hamiltonian acting on the automatic time-average lift
is exactly the semigroup finite-difference quotient. -/
theorem restrictedHamiltonian_approximateVector
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonTimeAverageApproximateEigenpairStrongLimitData
      A hInnerSymmetric hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) :
    T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
        (R.approximateVector n k) =
      R.differenceQuotientValue n k := by
  apply Subtype.ext
  change
    T.closedRightHamiltonian
        (T.vacuumOrthogonalAmbientDomainPoint (R.approximateVector n k)) =
      T.rightHamiltonianDifferenceQuotient
        (R.ambientEmbeddedVector n k) (R.width n)
  have hDomainPoint :
      T.vacuumOrthogonalAmbientDomainPoint (R.approximateVector n k) =
        R.closedAmbientVector n k := by
    apply Subtype.ext
    rfl
  rw [hDomainPoint]
  calc
    T.closedRightHamiltonian (R.closedAmbientVector n k) =
        T.rightHamiltonianLinearPMap (R.timeAveragedCoreVector n k) :=
      LinearPMap.apply_domainPointOfLE
        T.rightHamiltonianLinearPMap_le_closedRightHamiltonian
        (R.timeAveragedCoreVector n k)
    _ = T.rightHamiltonianDifferenceQuotient
        (R.ambientEmbeddedVector n k) (R.width n) :=
      T.rightHamiltonianLinearPMap_timeAverageRightHamiltonianDomain
        (R.width n) (R.ambientEmbeddedVector n k)

/-- Every unsmoothed embedded selected eigenvector has unit norm. -/
theorem embeddedVector_norm
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonTimeAverageApproximateEigenpairStrongLimitData
      A hInnerSymmetric hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) :
    ‖R.embeddedVector n k‖ = 1 := by
  rw [embeddedVector, R.realization.excitationEmbed_norm]
  simpa [finiteVector,
    FiniteWilsonFiniteDimensionalHamiltonianConfluentSpectralWitnessData.spectralVector,
    FiniteDimensionalSymmetricEigenbasisSelectionData.spectralVector] using
    ((F.hamiltonianSymmetric n).eigenvectorBasis F.stateFinrank).orthonormal.norm_eq_one
      ((R.finiteIndexEquiv n k).1)

/-- Strong convergence of the unsmoothed isometric embeddings fixes the limiting
continuum vector norm at one. -/
theorem spectralVector_norm
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonTimeAverageApproximateEigenpairStrongLimitData
      A hInnerSymmetric hSelf F nodes orderCap)
    (k : R.SpectralIndex) :
    ‖R.spectralVector k‖ = 1 := by
  have hNormTendsto := (R.embeddedVector_tendsto k).norm
  have hConstant :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop
        (nhds ‖R.spectralVector k‖) := by
    simpa only [R.embeddedVector_norm] using hNormTendsto
  exact tendsto_nhds_unique hConstant tendsto_const_nhds

/-- Limiting continuum spectral vectors are nonzero. -/
theorem spectralVector_ne_zero
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonTimeAverageApproximateEigenpairStrongLimitData
      A hInnerSymmetric hSelf F nodes orderCap)
    (k : R.SpectralIndex) :
    R.spectralVector k ≠ 0 := by
  intro hzero
  have hnorm := R.spectralVector_norm k
  rw [hzero, norm_zero] at hnorm
  norm_num at hnorm

/-- Ambient convergence of the isometrically embedded finite selected vector. -/
theorem ambientEmbeddedVector_tendsto
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonTimeAverageApproximateEigenpairStrongLimitData
      A hInnerSymmetric hSelf F nodes orderCap)
    (k : R.SpectralIndex) :
    Tendsto (fun n => R.ambientEmbeddedVector n k) atTop
      (nhds (((R.spectralVector k : P.VacuumOrthogonalHilbert) :
        P.PhysicalHilbert))) := by
  exact (continuous_subtype_val.tendsto (R.spectralVector k)).comp
    (R.embeddedVector_tendsto k)

/-- Shrinking time averages converge to the same continuum spectral vector as
the unsmoothed embedded finite eigenvectors. -/
theorem timeAveragedVector_tendsto
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonTimeAverageApproximateEigenpairStrongLimitData
      A hInnerSymmetric hSelf F nodes orderCap)
    (k : R.SpectralIndex) :
    Tendsto (fun n => R.timeAveragedVector n k) atTop
      (nhds (R.spectralVector k)) := by
  apply (IsInducing.subtypeVal.tendsto_nhds_iff).2
  simpa [timeAveragedVector] using
    T.timeAverage_tendsto_of_width_tendsto_zero_of_vector_tendsto
      R.width_pos R.width_tendsto_zero
      (R.ambientEmbeddedVector_tendsto k)

/-- Time averaging changes the moving embedded vector by a strongly vanishing
amount. -/
theorem timeAveragedVector_sub_embeddedVector_tendsto_zero
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonTimeAverageApproximateEigenpairStrongLimitData
      A hInnerSymmetric hSelf F nodes orderCap)
    (k : R.SpectralIndex) :
    Tendsto
      (fun n => R.timeAveragedVector n k - R.embeddedVector n k)
      atTop (nhds 0) := by
  simpa only [sub_self] using
    (R.timeAveragedVector_tendsto k).sub (R.embeddedVector_tendsto k)

/-- The finite Hamiltonian eigen-equation survives the continuum excitation
embedding. -/
theorem excitationEmbed_hamiltonian_finiteVector
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonTimeAverageApproximateEigenpairStrongLimitData
      A hInnerSymmetric hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) :
    R.realization.excitationEmbed n
        (F.hamiltonian n (R.finiteVector n k)) =
      R.approximateValue n k • R.embeddedVector n k := by
  rw [(R.finiteWitness n).hamiltonian_apply_spectralVector]
  rfl

/-- Semigroup difference-quotient compatibility lifts from the ambient Hilbert
space to the complete excitation carrier. -/
theorem differenceQuotientCompatibility_tendsto_zero_excitation
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonTimeAverageApproximateEigenpairStrongLimitData
      A hInnerSymmetric hSelf F nodes orderCap)
    (k : R.SpectralIndex) :
    Tendsto
      (fun n =>
        R.differenceQuotientValue n k -
          R.realization.excitationEmbed n
            (F.hamiltonian n (R.finiteVector n k)))
      atTop (nhds 0) := by
  apply (IsInducing.subtypeVal.tendsto_nhds_iff).2
  simpa [differenceQuotientValue, ambientEmbeddedVector, embeddedVector,
    finiteVector] using
    R.semigroupDifferenceQuotientCompatibility_tendsto_zero k

/-- The discrepancy between the embedded finite Hamiltonian action and the
spectral value acting on the time-averaged vector vanishes strongly. -/
theorem embeddedHamiltonian_sub_value_timeAverage_tendsto_zero
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonTimeAverageApproximateEigenpairStrongLimitData
      A hInnerSymmetric hSelf F nodes orderCap)
    (k : R.SpectralIndex) :
    Tendsto
      (fun n =>
        R.realization.excitationEmbed n
            (F.hamiltonian n (R.finiteVector n k)) -
          R.approximateValue n k • R.timeAveragedVector n k)
      atTop (nhds 0) := by
  have hScaled :
      Tendsto
        (fun n =>
          R.approximateValue n k •
            (R.embeddedVector n k - R.timeAveragedVector n k))
        atTop (nhds 0) := by
    have hDifference :
        Tendsto
          (fun n => R.embeddedVector n k - R.timeAveragedVector n k)
          atTop (nhds 0) := by
      simpa only [neg_sub] using
        (R.timeAveragedVector_sub_embeddedVector_tendsto_zero k).neg
    simpa only [smul_zero] using
      (R.approximateValue_tendsto k).smul hDifference
  simpa [R.excitationEmbed_hamiltonian_finiteVector, smul_sub] using hScaled

/-- The time-averaged vectors form strong approximate eigenpairs for the closed
continuum excitation Hamiltonian. -/
theorem residual_tendsto_zero
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonTimeAverageApproximateEigenpairStrongLimitData
      A hInnerSymmetric hSelf F nodes orderCap)
    (k : R.SpectralIndex) :
    Tendsto
      (fun n =>
        T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
            (R.approximateVector n k) -
          R.approximateValue n k •
            (R.approximateVector n k : P.VacuumOrthogonalHilbert))
      atTop (nhds 0) := by
  have hsum :=
    (R.differenceQuotientCompatibility_tendsto_zero_excitation k).add
      (R.embeddedHamiltonian_sub_value_timeAverage_tendsto_zero k)
  simpa only [R.restrictedHamiltonian_approximateVector,
    R.approximateVector_coe, sub_add_sub_cancel] using hsum

/-- Shrinking-time semigroup difference quotients construct the exact continuum
approximate-eigenpair strong-limit package. -/
noncomputable def toContinuumResolventApproximateEigenpairStrongLimitData
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonTimeAverageApproximateEigenpairStrongLimitData
      A hInnerSymmetric hSelf F nodes orderCap) :
    A.toVacuumSemigroupGapSlope.ContinuumResolventApproximateEigenpairStrongLimitData
      T hSelf nodes orderCap :=
  { SpectralIndex := R.SpectralIndex
    spectralFintype := R.spectralFintype
    approximateValue := R.approximateValue
    spectralValue := R.spectralValue
    spectralValue_injective := R.spectralValue_injective
    spectralCard := by
      calc
        Fintype.card R.SpectralIndex =
            Fintype.card (R.finiteWitness 0).SpectralIndex :=
          Fintype.card_congr (R.finiteIndexEquiv 0)
        _ = nodes.card * orderCap := (R.finiteWitness 0).spectralCard
    approximateVector := R.approximateVector
    spectralVector := R.spectralVector
    spectralVector_ne_zero := R.spectralVector_ne_zero
    approximateValue_tendsto := by
      intro k
      simpa [approximateValue] using R.approximateValue_tendsto k
    approximateVector_tendsto := by
      intro k
      simpa only [R.approximateVector_coe] using R.timeAveragedVector_tendsto k
    residual_tendsto_zero := R.residual_tendsto_zero }

/-- Time-averaged common-carrier Wilson spectra supply continuum confluent
resolvent linear independence. -/
theorem continuumResolventConfluentCauchy_linearIndependent
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonTimeAverageApproximateEigenpairStrongLimitData
      A hInnerSymmetric hSelf F nodes orderCap)
    (hP : P.IsNormalized) :
    LinearIndependent ℝ
      (fun p : nodes × Fin orderCap =>
        ContinuousLinearMap.positivePowerJetOperatorFamily
          (fun sigma : A.toVacuumSemigroupGapSlope.BelowHalfMassShift =>
            A.toVacuumSemigroupGapSlope.vacuumOrthogonalContinuumRealResolvent
              T hP hInnerSymmetric hSelf sigma.property)
          (p.1.1, p.2.1)) :=
  A.toVacuumSemigroupGapSlope
    |>.continuumResolventConfluentCauchy_linearIndependent_of_approximateEigenpairStrongLimit
      T hP hInnerSymmetric hSelf nodes orderCap
      R.toContinuumResolventApproximateEigenpairStrongLimitData

/-- The same shrinking-time construction gives support-local continuum
positive-power jet coefficient-map faithfulness. -/
theorem continuumResolventPositivePowerJetCoefficientMapsIndependent
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonTimeAverageApproximateEigenpairStrongLimitData
      A hInnerSymmetric hSelf F nodes orderCap)
    (hP : P.IsNormalized)
    (left right : ContinuousLinearMap.PositivePowerJetCoefficientMap
      A.toVacuumSemigroupGapSlope.BelowHalfMassShift)
    (hFit : A.toVacuumSemigroupGapSlope.PositivePowerJetCoefficientMapsFitWindow
      nodes orderCap left right) :
    A.toVacuumSemigroupGapSlope.ContinuumResolventPositivePowerJetCoefficientMapsIndependent
      T hP hInnerSymmetric hSelf left right :=
  A.toVacuumSemigroupGapSlope
    |>.continuumResolventPositivePowerJetCoefficientMapsIndependent_of_approximateEigenpairStrongLimit
      T hP hInnerSymmetric hSelf nodes orderCap
      R.toContinuumResolventApproximateEigenpairStrongLimitData
      left right hFit

end PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonTimeAverageApproximateEigenpairStrongLimitData

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
