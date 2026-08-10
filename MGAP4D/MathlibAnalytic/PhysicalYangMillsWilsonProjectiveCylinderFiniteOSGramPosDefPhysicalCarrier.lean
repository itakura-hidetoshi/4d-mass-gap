import MGAP4D.MathlibAnalytic.FiniteLinearIndependentEventualLowerFrame
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSDenseStateMap
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingContinuumSymmetry
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSContinuumVacuum
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonBoundaryMarginalProjectiveL2Carrier
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonCommonProductFiniteOSGramPosDefPhysicalCarrier
import Mathlib.Data.Finset.Union

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped ENNReal

noncomputable section

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}

/-- Repackage the positive-time submodule used by the OS bilinear form as the
opaque OS carrier, bundled linearly.  This is the subtype-safe bridge needed
for finite linear combinations. -/
noncomputable def positiveTimeSubmoduleCarrierLinearMap
    (P : D.OSPreHilbertData) :
    D.positiveTimeSubalgebra.toSubmodule →ₗ[ℝ] P.Carrier where
  toFun := fun F =>
    { observable := F.1.1
      gaugeInvariant := F.1.2
      positiveTime := F.2 }
  map_add' := by
    intro F G
    apply Carrier.observable_injective P
    rfl
  map_smul' := by
    intro r F
    apply Carrier.observable_injective P
    rfl

@[simp] theorem toPositiveTime_positiveTimeSubmoduleCarrierLinearMap
    (P : D.OSPreHilbertData)
    (F : D.positiveTimeSubalgebra.toSubmodule) :
    P.toPositiveTime (P.positiveTimeSubmoduleCarrierLinearMap F) = F := by
  apply Subtype.ext
  rfl

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

/-- Send an actual approximating positive-time Wilson observable into the one
common projective-limit continuum `L²` carrier.

The map is the composition

`positive time → OS carrier → completed finite OS Hilbert → projective marginal L²
→ continuum projective L²`.

Every factor is linear, and every factor after the first is theorem-generated
isometric data already present in the Wilson/projective spine. -/
noncomputable def physicalYangMillsProjectivePositiveTimeL2LinearMap
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
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout Q F)
    (L : EuclideanYangMillsProjectiveLimitMeasure F)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ) :
    D.positiveTimeSubalgebra.toSubmodule →ₗ[ℝ]
      Lp ℝ 2 L.continuumMeasure := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  exact
    (L.finiteMarginalL2Pullback (R.marginalIndex n)).toLinearMap.comp
      ((R.finiteOSMarginalLinearIsometry hInvariant n).toLinearMap.comp
        (Pn.physicalStateLinearMap.comp
          Pn.positiveTimeSubmoduleCarrierLinearMap))

/-- The norm squared of the common projective `L²` image is exactly the actual
finite-volume OS quadratic value. -/
theorem physical_yang_mills_projectivePositiveTimeL2_norm_sq_eq_osBilinForm
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
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout Q F)
    (L : EuclideanYangMillsProjectiveLimitMeasure F)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (G : D.positiveTimeSubalgebra.toSubmodule) :
    ‖physicalYangMillsProjectivePositiveTimeL2LinearMap
        R L hInvariant n G‖ ^ 2 =
      D.osBilinForm
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)
        G G := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  let c : Pn.Carrier := Pn.positiveTimeSubmoduleCarrierLinearMap G
  calc
    ‖physicalYangMillsProjectivePositiveTimeL2LinearMap
        R L hInvariant n G‖ ^ 2 =
        ‖L.finiteMarginalL2Pullback (R.marginalIndex n)
          (R.finiteOSMarginalLinearIsometry hInvariant n
            (Pn.physicalState c))‖ ^ 2 := by
      rfl
    _ = ‖R.finiteOSMarginalLinearIsometry hInvariant n
          (Pn.physicalState c)‖ ^ 2 := by
      rw [L.finiteMarginalL2Pullback_norm]
    _ = ‖Pn.physicalState c‖ ^ 2 := by
      rw [R.finiteOSMarginalLinearIsometry_norm]
    _ = ‖c‖ ^ 2 := by
      rw [Pn.norm_physicalState]
    _ = Pn.osQuadraticValue c :=
      (Pn.osQuadraticValue_eq_norm_sq c).symm
    _ = D.osBilinForm
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)
        G G := by
      change D.osBilinForm Pn.omega
          (Pn.toPositiveTime c) (Pn.toPositiveTime c) =
        D.osBilinForm
          (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n) G G
      rw [PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.toPositiveTime_positiveTimeSubmoduleCarrierLinearMap]
      rfl

/-- Projective `L²` eventual coherence plus finite linear independence is enough
to generate strict continuum OS Gram matrices.

Unlike the all-volume coercivity package, this datum only asks that every
selected observable become exactly one fixed continuum projective `L²` vector
on a scale tail.  Quantitative coercivity is then generated automatically from
finite-dimensional linear independence. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSProjectiveL2EventuallyCoherentPhysicalCarrierData
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (F : EuclideanYangMillsProjectiveCylinderFamily)
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout Q F)
    (L : EuclideanYangMillsProjectiveLimitMeasure F)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)) where
  observable : ℕ → D.positiveTimeSubalgebra.toSubmodule
  continuumVector : ℕ → Lp ℝ 2 L.continuumMeasure
  eventually_projective_eq : ∀ k,
    ∀ᶠ n in atTop,
      physicalYangMillsProjectivePositiveTimeL2LinearMap
        R L hInvariant n (observable k) = continuumVector k
  finiteLinearIndependent : ∀ s : Finset ℕ,
    LinearIndependent ℝ (fun i : s => continuumVector (i : ℕ))

namespace PhysicalYangMillsEvenPeriodicWilsonOSProjectiveL2EventuallyCoherentPhysicalCarrierData

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
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout Q F}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}

/-- Finite projective `L²` linear independence generates a tail-uniform OS
coercivity constant for the same finite family. -/
theorem eventually_uniformFiniteOSCoercivity
    (J : PhysicalYangMillsEvenPeriodicWilsonOSProjectiveL2EventuallyCoherentPhysicalCarrierData
      S D halfExtent N hN beta hbeta Q F R L hInvariant)
    (s : Finset ℕ) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ n in atTop, ∀ x : s → ℝ,
        δ * (∑ i, x i ^ 2) ≤
          D.osBilinForm
            (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)
            (∑ i : s, x i • J.observable (i : ℕ))
            (∑ i : s, x i • J.observable (i : ℕ)) := by
  classical
  rcases exists_pos_sum_sq_le_norm_sq_of_linearIndependent
      (fun i : s => J.continuumVector (i : ℕ))
      (J.finiteLinearIndependent s) with ⟨δ, hδ, hlower⟩
  refine ⟨δ, hδ, ?_⟩
  have heq : ∀ᶠ n in atTop, ∀ i : s,
      physicalYangMillsProjectivePositiveTimeL2LinearMap
          R L hInvariant n (J.observable (i : ℕ)) =
        J.continuumVector (i : ℕ) := by
    rw [Filter.eventually_all]
    intro i
    exact J.eventually_projective_eq (i : ℕ)
  filter_upwards [heq] with n hn
  intro x
  let T : D.positiveTimeSubalgebra.toSubmodule →ₗ[ℝ]
      Lp ℝ 2 L.continuumMeasure :=
    physicalYangMillsProjectivePositiveTimeL2LinearMap R L hInvariant n
  have hmap_finset : ∀ t : Finset s,
      T (t.sum (fun i => x i • J.observable (i : ℕ))) =
        t.sum (fun i => x i • J.continuumVector (i : ℕ)) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        simpa using T.map_zero
    | @insert i t hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi]
        calc
          T (x i • J.observable (i : ℕ) +
              t.sum (fun j => x j • J.observable (j : ℕ))) =
              T (x i • J.observable (i : ℕ)) +
                T (t.sum (fun j => x j • J.observable (j : ℕ))) :=
            T.map_add _ _
          _ = x i • J.continuumVector (i : ℕ) +
                t.sum (fun j => x j • J.continuumVector (j : ℕ)) := by
            rw [T.map_smul, hn i, ih]
  have hmap :
      T (∑ i : s, x i • J.observable (i : ℕ)) =
        ∑ i : s, x i • J.continuumVector (i : ℕ) := by
    simpa using hmap_finset Finset.univ
  calc
    δ * (∑ i, x i ^ 2) ≤
        ‖∑ i : s, x i • J.continuumVector (i : ℕ)‖ ^ 2 :=
      hlower x
    _ = ‖T (∑ i : s, x i • J.observable (i : ℕ))‖ ^ 2 := by
      rw [hmap]
    _ = D.osBilinForm
          (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)
          (∑ i : s, x i • J.observable (i : ℕ))
          (∑ i : s, x i • J.observable (i : ℕ)) :=
      physical_yang_mills_projectivePositiveTimeL2_norm_sq_eq_osBilinForm
        R L hInvariant n _

/-- Projective cylinder tail coherence and finite linear independence pass to
strict positive definiteness of every continuum OS Gram matrix. -/
theorem continuum_osGram_posDef
    (J : PhysicalYangMillsEvenPeriodicWilsonOSProjectiveL2EventuallyCoherentPhysicalCarrierData
      S D halfExtent N hN beta hbeta Q F R L hInvariant)
    (s : Finset ℕ) :
    Matrix.PosDef
      ((fun i j : s =>
        D.osBilinForm
          (physicalYangMillsContinuumGaugeInvariantWeakStarState S)
          (J.observable (i : ℕ))
          (J.observable (j : ℕ))) : Matrix s s ℝ) := by
  classical
  letI : AddCommGroup D.positiveTimeSubalgebra.toSubmodule :=
    Submodule.addCommGroup
      (R := ℝ)
      (M := physicalYangMillsGaugeInvariantObservableSubalgebra S)
      (p := D.positiveTimeSubalgebra.toSubmodule)
  letI : Module ℝ D.positiveTimeSubalgebra.toSubmodule :=
    Submodule.module
      (R := ℝ)
      (M := physicalYangMillsGaugeInvariantObservableSubalgebra S)
      (p := D.positiveTimeSubalgebra.toSubmodule)
  let w : s → D.positiveTimeSubalgebra.toSubmodule := fun i =>
    J.observable (i : ℕ)
  let A : ℕ → Matrix s s ℝ := fun n i j =>
    D.osBilinForm
      (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)
      (w i) (w j)
  let A_limit : Matrix s s ℝ := fun i j =>
    D.osBilinForm
      (physicalYangMillsContinuumGaugeInvariantWeakStarState S)
      (w i) (w j)
  rcases J.eventually_uniformFiniteOSCoercivity s with
    ⟨δ, hδ, hcoercive⟩
  have hSymm :
      (D.osBilinForm
        (physicalYangMillsContinuumGaugeInvariantWeakStarState S)).IsSymm :=
    D.osBilinForm_isSymm
      (physicalYangMillsContinuumGaugeInvariantWeakStarState S)
      (physical_yang_mills_gaugeInvariantWeakStarReflectionInvariance_passes_to_limit
        S D hInvariant)
  have hHermitian : A_limit.IsHermitian := by
    exact bilinForm_matrix_isHermitian_of_isSymm
      (D.osBilinForm
        (physicalYangMillsContinuumGaugeInvariantWeakStarState S))
      hSymm w
  have hTendsto : ∀ x : s → ℝ,
      Filter.Tendsto
        (fun n : ℕ => dotProduct (star x) (Matrix.mulVec (A n) x))
        atTop
        (nhds (dotProduct (star x) (Matrix.mulVec A_limit x))) := by
    intro x
    have h :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_osBilinForm_tendsto
        S D
        (∑ i : s, x i • w i)
        (∑ i : s, x i • w i)
    have hApprox :
        (fun n : ℕ => dotProduct (star x) (Matrix.mulVec (A n) x)) =
          (fun n : ℕ =>
            D.osBilinForm
              (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)
              (∑ i : s, x i • w i)
              (∑ i : s, x i • w i)) := by
      funext n
      have hq :=
        bilinForm_matrix_quadratic_eq
          (D.osBilinForm
            (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
          w x
      simpa only [A] using hq
    have hLimit :
        dotProduct (star x) (Matrix.mulVec A_limit x) =
          D.osBilinForm
            (physicalYangMillsContinuumGaugeInvariantWeakStarState S)
            (∑ i : s, x i • w i)
            (∑ i : s, x i • w i) := by
      have hq :=
        bilinForm_matrix_quadratic_eq
          (D.osBilinForm
            (physicalYangMillsContinuumGaugeInvariantWeakStarState S))
          w x
      simpa only [A_limit] using hq
    rw [hApprox, hLimit]
    exact h
  have hCoercive : ∀ᶠ n in atTop, ∀ x : s → ℝ,
      δ * (∑ i, x i ^ 2) ≤
        dotProduct (star x) (Matrix.mulVec (A n) x) := by
    filter_upwards [hcoercive] with n hn
    intro x
    have hq :
        dotProduct (star x) (Matrix.mulVec (A n) x) =
          D.osBilinForm
            (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)
            (∑ i : s, x i • w i)
            (∑ i : s, x i • w i) := by
      have h :=
        bilinForm_matrix_quadratic_eq
          (D.osBilinForm
            (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
          w x
      simpa only [A] using h
    calc
      δ * (∑ i, x i ^ 2) ≤
          D.osBilinForm
            (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)
            (∑ i : s, x i • w i)
            (∑ i : s, x i • w i) := by
        simpa only [w] using hn x
      _ = dotProduct (star x) (Matrix.mulVec (A n) x) := hq.symm
  have hPosDef :=
    matrix_posDef_of_eventually_uniform_quadratic_coercivity_tendsto
      A A_limit hHermitian δ hδ hTendsto hCoercive
  simpa [A_limit, w] using hPosDef

/-- The projective `L²` eventual-coherence datum theorem-generates the exact
finite positive-definite continuum Gram interface integrated in #1602. -/
noncomputable def toFiniteOSGramPosDefPhysicalCarrierData
    (J : PhysicalYangMillsEvenPeriodicWilsonOSProjectiveL2EventuallyCoherentPhysicalCarrierData
      S D halfExtent N hN beta hbeta Q F R L hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSCommonProductFiniteOSGramPosDefPhysicalCarrierData
      halfExtent N hN beta hbeta
      (physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
      (physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData_isNormalized
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant) where
  observable := fun n =>
    PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.positiveTimeSubmoduleCarrierLinearMap
      (physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
      (J.observable n)
  osGram_posDef := by
    intro s
    have h := J.continuum_osGram_posDef s
    simpa using h

end PhysicalYangMillsEvenPeriodicWilsonOSProjectiveL2EventuallyCoherentPhysicalCarrierData

/-- Finite projective cylinder data reducing eventual coherence to actual
finite marginal transition compatibility and finite-marginal linear
independence. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSFiniteProjectiveCylinderLinearIndependentData
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (F : EuclideanYangMillsProjectiveCylinderFamily)
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout Q F)
    (L : EuclideanYangMillsProjectiveLimitMeasure F)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)) where
  observable : ℕ → D.positiveTimeSubalgebra.toSubmodule
  cylinderIndex : ℕ → Finset EuclideanFourSpace
  cylinderVector : ∀ k,
    Lp ℝ 2 (F.finiteMarginal (cylinderIndex k))
  supportEventually : ∀ k,
    ∀ᶠ n in atTop, cylinderIndex k ⊆ R.marginalIndex n
  finiteImage_eq_transition : ∀ k n
      (h : cylinderIndex k ⊆ R.marginalIndex n),
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    R.finiteOSMarginalLinearIsometry hInvariant n
        (Pn.physicalState
          (Pn.positiveTimeSubmoduleCarrierLinearMap (observable k))) =
      EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
        (F := F) h (cylinderVector k)
  finiteCommonMarginalLinearIndependent : ∀ s : Finset ℕ,
    LinearIndependent ℝ
      (fun i : s =>
        EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
          (F := F)
          (Finset.subset_biUnion_of_mem cylinderIndex i.property)
          (cylinderVector (i : ℕ)))

namespace PhysicalYangMillsEvenPeriodicWilsonOSFiniteProjectiveCylinderLinearIndependentData

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
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout Q F}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}

/-- Actual finite projective cylinder compatibility and finite-marginal linear
independence generate the eventual-coherence datum above. -/
noncomputable def toProjectiveL2EventuallyCoherentPhysicalCarrierData
    (C : PhysicalYangMillsEvenPeriodicWilsonOSFiniteProjectiveCylinderLinearIndependentData
      S D halfExtent N hN beta hbeta Q F R L hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSProjectiveL2EventuallyCoherentPhysicalCarrierData
      S D halfExtent N hN beta hbeta Q F R L hInvariant where
  observable := C.observable
  continuumVector := fun k =>
    L.finiteMarginalL2Pullback (C.cylinderIndex k) (C.cylinderVector k)
  eventually_projective_eq := by
    intro k
    filter_upwards [C.supportEventually k] with n hn
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    calc
      physicalYangMillsProjectivePositiveTimeL2LinearMap
          R L hInvariant n (C.observable k) =
        L.finiteMarginalL2Pullback (R.marginalIndex n)
          (R.finiteOSMarginalLinearIsometry hInvariant n
            (Pn.physicalState
              (Pn.positiveTimeSubmoduleCarrierLinearMap (C.observable k)))) := by
        rfl
      _ = L.finiteMarginalL2Pullback (R.marginalIndex n)
          (EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
            (F := F) hn (C.cylinderVector k)) := by
        rw [C.finiteImage_eq_transition k n hn]
      _ = L.finiteMarginalL2Pullback (C.cylinderIndex k)
          (C.cylinderVector k) :=
        (L.finiteMarginalL2Pullback_compatible hn (C.cylinderVector k)).symm
  finiteLinearIndependent := by
    intro s
    let commonIndex : Finset EuclideanFourSpace :=
      s.biUnion C.cylinderIndex
    let e :
        Lp ℝ 2 (F.finiteMarginal commonIndex) →ₗ[ℝ]
          Lp ℝ 2 L.continuumMeasure :=
      (L.finiteMarginalL2Pullback commonIndex).toLinearMap
    let u : s → Lp ℝ 2 (F.finiteMarginal commonIndex) := fun i =>
      EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
        (F := F)
        (Finset.subset_biUnion_of_mem C.cylinderIndex i.property)
        (C.cylinderVector (i : ℕ))
    have hu : LinearIndependent ℝ u := by
      simpa [u, commonIndex] using C.finiteCommonMarginalLinearIndependent s
    have heker : LinearMap.ker e = ⊥ :=
      LinearMap.ker_eq_bot.mpr
        (L.finiteMarginalL2Pullback_injective commonIndex)
    have hmap : LinearIndependent ℝ (e ∘ u) :=
      hu.map' e heker
    have hfamily :
        (fun i : s =>
          L.finiteMarginalL2Pullback (C.cylinderIndex (i : ℕ))
            (C.cylinderVector (i : ℕ))) = e ∘ u := by
      funext i
      exact L.finiteMarginalL2Pullback_compatible
        (Finset.subset_biUnion_of_mem C.cylinderIndex i.property)
        (C.cylinderVector (i : ℕ))
    rw [hfamily]
    exact hmap

/-- Finite projective cylinder compatibility plus finite common-marginal linear
independence theorem-generates the strict continuum finite-Gram datum. -/
noncomputable def toFiniteOSGramPosDefPhysicalCarrierData
    (C : PhysicalYangMillsEvenPeriodicWilsonOSFiniteProjectiveCylinderLinearIndependentData
      S D halfExtent N hN beta hbeta Q F R L hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSCommonProductFiniteOSGramPosDefPhysicalCarrierData
      halfExtent N hN beta hbeta
      (physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
      (physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData_isNormalized
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant) :=
  (C.toProjectiveL2EventuallyCoherentPhysicalCarrierData).toFiniteOSGramPosDefPhysicalCarrierData

end PhysicalYangMillsEvenPeriodicWilsonOSFiniteProjectiveCylinderLinearIndependentData

end

end MathlibAnalytic
end MGAP4D