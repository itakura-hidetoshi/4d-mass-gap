import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumOrthogonalRealResolventParameterContinuity
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Tactic

noncomputable section

open Set Filter Topology
open scoped InnerProductSpace LinearPMap ContDiff

namespace LinearPMap

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A total real-parameter representative of the sub-mass resolvent family.
Outside the open sub-mass interval it is set to zero.  All analytic statements
below are made at, or within, the open interval where this auxiliary choice is
irrelevant. -/
noncomputable def realResolventOn
    (A : E →ₗ.[ℝ] E) {mass : ℝ}
    (hSelf : IsSelfAdjoint A)
    (hgap : ∀ x : A.domain,
      mass * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E))
    (lambda : ℝ) : E →L[ℝ] E :=
  if hlambda : lambda < mass then
    A.realResolvent hSelf hlambda hgap
  else
    0

@[simp] theorem realResolventOn_of_lt
    (A : E →ₗ.[ℝ] E) {mass lambda : ℝ}
    (hSelf : IsSelfAdjoint A)
    (hgap : ∀ x : A.domain,
      mass * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E))
    (hlambda : lambda < mass) :
    A.realResolventOn hSelf hgap lambda =
      A.realResolvent hSelf hlambda hgap := by
  simp [realResolventOn, hlambda]

/-- The total representative restricts to the already constructed continuous
resolvent family on the open sub-mass interval. -/
theorem realResolventOn_continuousOn
    (A : E →ₗ.[ℝ] E) {mass : ℝ}
    (hSelf : IsSelfAdjoint A)
    (hgap : ∀ x : A.domain,
      mass * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E)) :
    ContinuousOn (A.realResolventOn hSelf hgap) (Set.Iio mass) := by
  rw [continuousOn_iff_continuous_restrict]
  have heq :
      (Set.Iio mass).restrict (A.realResolventOn hSelf hgap) =
        A.realResolventFamily hSelf hgap := by
    funext lambda
    exact A.realResolventOn_of_lt hSelf hgap lambda.property
  rw [heq]
  exact A.realResolventFamily_continuous hSelf hgap

/-- The operator-norm derivative of the real resolvent within the sub-mass
interval is the square of the resolvent. -/
theorem realResolventOn_hasDerivWithinAt
    (A : E →ₗ.[ℝ] E) {mass lambda : ℝ}
    (hSelf : IsSelfAdjoint A)
    (hgap : ∀ x : A.domain,
      mass * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E))
    (hlambda : lambda < mass) :
    HasDerivWithinAt
      (A.realResolventOn hSelf hgap)
      ((A.realResolvent hSelf hlambda hgap).comp
        (A.realResolvent hSelf hlambda hgap))
      (Set.Iio mass) lambda := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  let Rlambda : E →L[ℝ] E := A.realResolvent hSelf hlambda hgap
  have hres0 :
      Tendsto (A.realResolventOn hSelf hgap)
        (𝓝[Set.Iio mass] lambda)
        (𝓝 (A.realResolventOn hSelf hgap lambda)) :=
    A.realResolventOn_continuousOn hSelf hgap lambda hlambda
  have hres :
      Tendsto (A.realResolventOn hSelf hgap)
        (𝓝[Set.Iio mass] lambda) (𝓝 Rlambda) := by
    simpa [Rlambda] using hres0
  have hres' :
      Tendsto (A.realResolventOn hSelf hgap)
        (𝓝[Set.Iio mass \ {lambda}] lambda) (𝓝 Rlambda) :=
    hres.mono_left <| nhdsWithin_mono _ <| by
      intro mu hmu
      exact hmu.1
  have hcomp :
      Tendsto
        (fun mu => (A.realResolventOn hSelf hgap mu).comp Rlambda)
        (𝓝[Set.Iio mass \ {lambda}] lambda)
        (𝓝 (Rlambda.comp Rlambda)) := by
    exact
      (continuous_id.clm_comp_const Rlambda).continuousAt.tendsto.comp hres'
  apply hcomp.congr'
  filter_upwards [self_mem_nhdsWithin] with mu hmu
  rcases hmu with ⟨hmuMass, hmuNe⟩
  have hne : mu - lambda ≠ 0 := by
    apply sub_ne_zero.mpr
    simpa only [mem_singleton_iff] using hmuNe
  rw [slope_def_module,
    A.realResolventOn_of_lt hSelf hgap hmuMass,
    A.realResolventOn_of_lt hSelf hgap hlambda,
    A.realResolvent_sub_eq_smul_comp hSelf hmuMass hlambda hgap,
    inv_smul_smul₀ hne]

/-- Since the sub-mass interval is open, the within-derivative is the ordinary
operator-norm derivative at every sub-mass parameter. -/
theorem realResolventOn_hasDerivAt
    (A : E →ₗ.[ℝ] E) {mass lambda : ℝ}
    (hSelf : IsSelfAdjoint A)
    (hgap : ∀ x : A.domain,
      mass * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E))
    (hlambda : lambda < mass) :
    HasDerivAt
      (A.realResolventOn hSelf hgap)
      ((A.realResolvent hSelf hlambda hgap).comp
        (A.realResolvent hSelf hlambda hgap))
      lambda :=
  (A.realResolventOn_hasDerivWithinAt hSelf hgap hlambda).hasDerivAt
    (Iio_mem_nhds hlambda)

/-- Explicit derivative formula for the total representative at every real
parameter below the Rayleigh threshold. -/
theorem realResolventOn_deriv
    (A : E →ₗ.[ℝ] E) {mass lambda : ℝ}
    (hSelf : IsSelfAdjoint A)
    (hgap : ∀ x : A.domain,
      mass * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E))
    (hlambda : lambda < mass) :
    deriv (A.realResolventOn hSelf hgap) lambda =
      (A.realResolvent hSelf hlambda hgap).comp
        (A.realResolvent hSelf hlambda hgap) :=
  (A.realResolventOn_hasDerivAt hSelf hgap hlambda).deriv

/-- The real resolvent is differentiable throughout the open sub-mass
interval. -/
theorem realResolventOn_differentiableOn
    (A : E →ₗ.[ℝ] E) {mass : ℝ}
    (hSelf : IsSelfAdjoint A)
    (hgap : ∀ x : A.domain,
      mass * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E)) :
    DifferentiableOn ℝ (A.realResolventOn hSelf hgap) (Set.Iio mass) := by
  intro lambda hlambda
  exact
    (A.realResolventOn_hasDerivWithinAt hSelf hgap hlambda).differentiableWithinAt

/-- The derivative of the real resolvent is continuous on the open sub-mass
interval. -/
theorem realResolventOn_continuousOn_deriv
    (A : E →ₗ.[ℝ] E) {mass : ℝ}
    (hSelf : IsSelfAdjoint A)
    (hgap : ∀ x : A.domain,
      mass * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E)) :
    ContinuousOn (deriv (A.realResolventOn hSelf hgap)) (Set.Iio mass) := by
  have hdiff := A.realResolventOn_differentiableOn hSelf hgap
  have hsquare :
      ContinuousOn
        (fun lambda =>
          (A.realResolventOn hSelf hgap lambda).comp
            (A.realResolventOn hSelf hgap lambda))
        (Set.Iio mass) :=
    (hdiff.clm_comp hdiff).continuousOn
  apply hsquare.congr
  intro lambda hlambda
  calc
    deriv (A.realResolventOn hSelf hgap) lambda =
        (A.realResolvent hSelf hlambda hgap).comp
          (A.realResolvent hSelf hlambda hgap) :=
      A.realResolventOn_deriv hSelf hgap hlambda
    _ = (A.realResolventOn hSelf hgap lambda).comp
          (A.realResolventOn hSelf hgap lambda) := by
      rw [A.realResolventOn_of_lt hSelf hgap hlambda]

/-- The sub-mass real resolvent family is continuously differentiable in the
operator-norm topology. -/
theorem realResolventOn_contDiffOn_one
    (A : E →ₗ.[ℝ] E) {mass : ℝ}
    (hSelf : IsSelfAdjoint A)
    (hgap : ∀ x : A.domain,
      mass * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E)) :
    ContDiffOn ℝ 1 (A.realResolventOn hSelf hgap) (Set.Iio mass) := by
  rw [show (1 : ℕ∞ω) = 0 + 1 from rfl,
    contDiffOn_succ_iff_deriv_of_isOpen Set.isOpen_Iio]
  refine ⟨A.realResolventOn_differentiableOn hSelf hgap, ?_, ?_⟩
  · simp
  · simpa only [contDiffOn_zero] using
      A.realResolventOn_continuousOn_deriv hSelf hgap

end LinearPMap

namespace MGAP4D
namespace MathlibAnalytic

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- The transferred Rayleigh bound in the exact domain type used by the
vacuum-orthogonal closed Hamiltonian resolvent. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolvent_rayleigh
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (y : (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf).domain) :
    G.mass * ‖(y : P.VacuumOrthogonalHilbert)‖ ^ 2 ≤
      inner ℝ
        (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf y)
        (y : P.VacuumOrthogonalHilbert) := by
  simpa only [vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint] using
    G.vacuumOrthogonalClosedRightHamiltonian_gap T hP
      ((T.closedRightHamiltonian_selfAdjoint_iff_isFormalAdjoint).mp hSelf) y

/-- A total real-parameter representative of the excitation resolvent. -/
noncomputable def FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolventOn
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) :
    ℝ → P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert :=
  LinearPMap.realResolventOn
    (A := T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf)
    (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint_isSelfAdjoint hP hSelf)
    (G.vacuumOrthogonalRealResolvent_rayleigh T hP hSelf)

@[simp] theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolventOn_of_lt
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ} (hlambda : lambda < G.mass) :
    G.vacuumOrthogonalRealResolventOn T hP hSelf lambda =
      G.vacuumOrthogonalRealResolvent T hP hSelf hlambda := by
  simp [vacuumOrthogonalRealResolventOn,
    FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolvent,
    LinearPMap.realResolventOn, hlambda]

/-- The excitation resolvent has operator-norm derivative equal to its square
at every real parameter below the transferred mass. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolventOn_hasDerivAt
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ} (hlambda : lambda < G.mass) :
    HasDerivAt
      (G.vacuumOrthogonalRealResolventOn T hP hSelf)
      ((G.vacuumOrthogonalRealResolvent T hP hSelf hlambda).comp
        (G.vacuumOrthogonalRealResolvent T hP hSelf hlambda))
      lambda := by
  simpa only [vacuumOrthogonalRealResolventOn,
    FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolvent] using
    (LinearPMap.realResolventOn_hasDerivAt
      (A := T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf)
      (hSelf :=
        T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint_isSelfAdjoint
          hP hSelf)
      (hgap := G.vacuumOrthogonalRealResolvent_rayleigh T hP hSelf)
      hlambda)

/-- Explicit derivative formula for the excitation resolvent. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolventOn_deriv
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ} (hlambda : lambda < G.mass) :
    deriv (G.vacuumOrthogonalRealResolventOn T hP hSelf) lambda =
      (G.vacuumOrthogonalRealResolvent T hP hSelf hlambda).comp
        (G.vacuumOrthogonalRealResolvent T hP hSelf hlambda) :=
  (G.vacuumOrthogonalRealResolventOn_hasDerivAt
    T hP hSelf hlambda).deriv

/-- The excitation resolvent is differentiable on the full real sub-mass
interval. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolventOn_differentiableOn
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) :
    DifferentiableOn ℝ
      (G.vacuumOrthogonalRealResolventOn T hP hSelf)
      (Set.Iio G.mass) := by
  intro lambda hlambda
  exact
    (G.vacuumOrthogonalRealResolventOn_hasDerivAt
      T hP hSelf hlambda).hasDerivWithinAt.differentiableWithinAt

/-- The excitation resolvent is `C¹` in operator norm throughout the open real
sub-mass interval. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolventOn_contDiffOn_one
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) :
    ContDiffOn ℝ 1
      (G.vacuumOrthogonalRealResolventOn T hP hSelf)
      (Set.Iio G.mass) := by
  simpa only [vacuumOrthogonalRealResolventOn] using
    (LinearPMap.realResolventOn_contDiffOn_one
      (A := T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf)
      (hSelf :=
        T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint_isSelfAdjoint
          hP hSelf)
      (hgap := G.vacuumOrthogonalRealResolvent_rayleigh T hP hSelf))

/-- Differentiability and `C¹` package for the excitation resolvent below the
transferred mass. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolventDerivative_package
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) :
    ContDiffOn ℝ 1
        (G.vacuumOrthogonalRealResolventOn T hP hSelf)
        (Set.Iio G.mass) ∧
      DifferentiableOn ℝ
        (G.vacuumOrthogonalRealResolventOn T hP hSelf)
        (Set.Iio G.mass) ∧
      ∀ {lambda : ℝ} (hlambda : lambda < G.mass),
        deriv (G.vacuumOrthogonalRealResolventOn T hP hSelf) lambda =
          (G.vacuumOrthogonalRealResolvent T hP hSelf hlambda).comp
            (G.vacuumOrthogonalRealResolvent T hP hSelf hlambda) :=
  ⟨G.vacuumOrthogonalRealResolventOn_contDiffOn_one T hP hSelf,
    G.vacuumOrthogonalRealResolventOn_differentiableOn T hP hSelf,
    fun hlambda =>
      G.vacuumOrthogonalRealResolventOn_deriv T hP hSelf hlambda⟩

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end MathlibAnalytic
end MGAP4D

end
