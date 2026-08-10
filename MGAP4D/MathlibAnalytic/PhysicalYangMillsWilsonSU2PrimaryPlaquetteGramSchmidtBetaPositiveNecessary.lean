import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2PrimaryPlaquetteGramSchmidtRawBoundaryMomentReadout
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryMomentBetaZeroDegeneracy
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped InnerProductSpace

noncomputable section

/-- Two distinct vectors of an orthonormal real `L²` sequence cannot both be
represented by a.e. constant functions.

This is a measure-independent Hilbert-space fact once the two constant
representatives already define `L²` vectors: pointwise commutativity gives a
nontrivial linear relation between the two vectors, while orthonormality forces
the coefficient of the second vector to vanish. -/
theorem orthonormal_nat_l2_zero_one_not_both_ae_constant
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (v : ℕ → Lp ℝ 2 μ)
    (hv : Orthonormal ℝ v)
    (h0 : ∃ c : ℝ, v 0 =ᵐ[μ] fun _ => c)
    (h1 : ∃ c : ℝ, v 1 =ᵐ[μ] fun _ => c) :
    False := by
  rcases h0 with ⟨c0, hv0⟩
  rcases h1 with ⟨c1, hv1⟩
  have hrel : c0 • v 1 = c1 • v 0 := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_smul c0 (v 1), Lp.coeFn_smul c1 (v 0), hv0, hv1] with x hs0 hs1 h0x h1x
    rw [hs0, hs1, h1x, h0x]
    simp [smul_eq_mul, mul_comm]
  have hinner := congrArg (fun w => inner ℝ (v 1) w) hrel
  have h11 : inner ℝ (v 1) (v 1) = 1 := by
    simpa using (orthonormal_iff_ite.mp hv 1 1)
  have h10 : inner ℝ (v 1) (v 0) = 0 := by
    exact hv.inner_eq_zero (by norm_num)
  have hc0 : c0 = 0 := by
    simpa [inner_smul_right, h11, h10] using hinner
  have hv0zero : v 0 = 0 := by
    apply Lp.ext
    filter_upwards [hv0] with x hx
    simpa [hc0] using hx
  have hnorm := hv.norm_eq_one 0
  rw [hv0zero, norm_zero] at hnorm
  norm_num at hnorm

local instance specialUnitaryTwoBetaNecessaryTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance specialUnitaryTwoBetaNecessaryCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance specialUnitaryTwoBetaNecessarySecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance specialUnitaryTwoBetaNecessaryMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance specialUnitaryTwoBetaNecessaryBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance specialUnitaryTwoBetaNecessaryNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

namespace PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtRawBoundaryMomentReadoutData

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta}
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout Q F}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}

/-- At any scale with zero coupling, the raw readout identity forces every
primary-plaquette Gram--Schmidt boundary mode to have an a.e. constant
representative. -/
theorem primaryPlaquetteGramSchmidtBoundaryHaarL2_ae_constant_of_beta_eq_zero
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtRawBoundaryMomentReadoutData
      S D halfExtent beta hbeta Q F R L hInvariant)
    (n k : ℕ)
    (hzero : beta n = 0) :
    ∃ c : ℝ,
      periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryHaarL2
          (halfExtent n) k =ᵐ[
        periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) 2]
        fun _ => c := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
      Q.toWeakStarBridge hInvariant n
  let Fn := Pn.positiveTimeSubmoduleCarrierLinearMap (C.observable k)
  let u :=
    physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
      S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
      Q.toWeakStarBridge hInvariant n Fn
  have hraw := C.rawBoundaryMoment_eq_primaryPlaquetteGramSchmidtBoundaryObservable k n
  have hraw0 :
      (fun b =>
        periodicHypercubicEvenBoundaryObservableMoment
          (halfExtent n) 2 specialUnitaryTwoWilsonRankPositive
          0 (by norm_num) u b) =ᵐ[
        periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) 2]
        periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryObservable
          (halfExtent n) k := by
    simpa [hzero, Pn, Fn, u] using hraw
  obtain ⟨c, hc⟩ :=
    periodicHypercubicEvenBoundaryObservableMoment_beta_zero_exists_constant
      (halfExtent n) 2 specialUnitaryTwoWilsonRankPositive (by norm_num) u
  refine ⟨c, ?_⟩
  have hmode :=
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryHaarL2_coeFn
      (halfExtent n) k
  exact hmode.trans (hraw0.symm.trans (Filter.Eventually.of_forall hc))

/-- The raw SU(2) Gram--Schmidt readout forces strict positive coupling at every
scale.

This is a consequence, not an added hypothesis.  If `beta n = 0`, the generic
finite-Wilson degeneracy theorem makes both the `k=0` and `k=1` boundary modes
a.e. constant, contradicting their theorem-generated orthonormality. -/
theorem beta_pos
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtRawBoundaryMomentReadoutData
      S D halfExtent beta hbeta Q F R L hInvariant)
    (n : ℕ) :
    0 < beta n := by
  have hne : beta n ≠ 0 := by
    intro hzero
    exact orthonormal_nat_l2_zero_one_not_both_ae_constant
      (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryHaarL2
        (halfExtent n))
      (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryHaarL2_orthonormal
        (halfExtent n))
      (C.primaryPlaquetteGramSchmidtBoundaryHaarL2_ae_constant_of_beta_eq_zero n 0 hzero)
      (C.primaryPlaquetteGramSchmidtBoundaryHaarL2_ae_constant_of_beta_eq_zero n 1 hzero)
  exact lt_of_le_of_ne (hbeta n) (Ne.symm hne)

/-- Audit-friendly family form: the raw readout route itself upgrades the
original nonnegative coupling sequence to a pointwise strictly positive one. -/
theorem beta_strictlyPositive
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtRawBoundaryMomentReadoutData
      S D halfExtent beta hbeta Q F R L hInvariant) :
    ∀ n, 0 < beta n :=
  C.beta_pos

end PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtRawBoundaryMomentReadoutData

end

end MathlibAnalytic
end MGAP4D
