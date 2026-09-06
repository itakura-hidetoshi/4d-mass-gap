import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenEightColorParallelHeatBathBlock
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonConditionalVarianceBCF
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathProjectionL2Identification
import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonOffLinkL2ProjectionAlgebra
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set

noncomputable section

set_option maxRecDepth 8192

private theorem periodic_even_bcf_abs_le_norm_l2
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration) :
    |O A| ≤ ‖O‖ := by
  simpa [Real.norm_eq_abs] using O.norm_coe_le_norm A

section FixedColorL2

variable (H N : ℕ)
variable (hN : 0 < N)
variable [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
variable (beta : ℝ) (hBeta : 0 ≤ beta)

local notation "C" =>
  periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN beta hBeta
local notation "L2" => Lp ℝ 2 (C).gibbsMeasure

/-- On bounded-continuous observables, the concrete one-link heat-bath
projections at distinct links of one canonical eight-color class commute.
This is the pointwise projection form of the already-canonical exact
same-color heat-bath-transform commutation theorem. -/
theorem periodicHypercubicEvenSpecialUnitary_singleLinkHeatBathProjection_commute_of_sameColor
    (O : BoundedContinuousFunction (C).base.Configuration ℝ)
    {target source : PeriodicHypercubicEvenEdge H}
    (hNe : source ≠ target)
    (hColor :
      periodicHypercubicEvenEdgeColor H target =
        periodicHypercubicEvenEdgeColor H source) :
    (C).singleLinkHeatBathProjection source
        ((C).singleLinkHeatBathProjection target O) =
      (C).singleLinkHeatBathProjection target
        ((C).singleLinkHeatBathProjection source O) := by
  change
    (C).singleLinkHeatBathTransform source
        ((C).singleLinkHeatBathTransform target O) =
      (C).singleLinkHeatBathTransform target
        ((C).singleLinkHeatBathTransform source O)
  exact
    periodicHypercubicEvenSpecialUnitary_singleLinkHeatBathTransform_commute_of_sameColor
      H N hN beta hBeta O O.continuous hNe hColor

/-- On the canonical bounded-continuous Gibbs `L²` core, the two abstract
`condExpL2` one-link projections commute at distinct links of one fixed color.
The proof identifies each abstract projection with the concrete Wilson
heat-bath kernel action and then applies exact same-color conditional locality. -/
theorem periodicHypercubicEvenSpecialUnitary_singleLinkHeatBathProjectionL2_comm_on_gibbsL2RepresentativeBCF_of_sameColor
    (O : BoundedContinuousFunction (C).base.Configuration ℝ)
    {target source : PeriodicHypercubicEvenEdge H}
    (hNe : source ≠ target)
    (hColor :
      periodicHypercubicEvenEdgeColor H target =
        periodicHypercubicEvenEdgeColor H source) :
    (C).singleLinkHeatBathProjectionL2 source
        ((C).singleLinkHeatBathProjectionL2 target
          ((C).gibbsL2RepresentativeBCF O)) =
      (C).singleLinkHeatBathProjectionL2 target
        ((C).singleLinkHeatBathProjectionL2 source
          ((C).gibbsL2RepresentativeBCF O)) := by
  let M : ℝ := ‖O‖
  have hM0 : 0 ≤ M := by
    dsimp [M]
    exact norm_nonneg _
  have hOStrong : StronglyMeasurable
      (O : (C).base.Configuration → ℝ) :=
    O.continuous.stronglyMeasurable
  have hOBound : ∀ A, |O A| ≤ M := by
    intro A
    dsimp [M]
    exact periodic_even_bcf_abs_le_norm_l2 O A
  have hTargetStrong : StronglyMeasurable
      ((C).singleLinkHeatBathProjection target O) :=
    continuous_compact_oriented_singleLinkHeatBathProjection_stronglyMeasurable
      C target O hOStrong
  have hTargetBound :
      ∀ A, |(C).singleLinkHeatBathProjection target O A| ≤ M :=
    continuous_compact_oriented_singleLinkHeatBathProjection_abs_le
      C target O hOStrong M hM0 hOBound
  have hSourceStrong : StronglyMeasurable
      ((C).singleLinkHeatBathProjection source O) :=
    continuous_compact_oriented_singleLinkHeatBathProjection_stronglyMeasurable
      C source O hOStrong
  have hSourceBound :
      ∀ A, |(C).singleLinkHeatBathProjection source O A| ≤ M :=
    continuous_compact_oriented_singleLinkHeatBathProjection_abs_le
      C source O hOStrong M hM0 hOBound
  have hSourceTargetStrong : StronglyMeasurable
      ((C).singleLinkHeatBathProjection source
        ((C).singleLinkHeatBathProjection target O)) :=
    continuous_compact_oriented_singleLinkHeatBathProjection_stronglyMeasurable
      C source ((C).singleLinkHeatBathProjection target O) hTargetStrong
  have hSourceTargetBound :
      ∀ A,
        |(C).singleLinkHeatBathProjection source
          ((C).singleLinkHeatBathProjection target O) A| ≤ M :=
    continuous_compact_oriented_singleLinkHeatBathProjection_abs_le
      C source ((C).singleLinkHeatBathProjection target O)
      hTargetStrong M hM0 hTargetBound
  have hTargetSourceStrong : StronglyMeasurable
      ((C).singleLinkHeatBathProjection target
        ((C).singleLinkHeatBathProjection source O)) :=
    continuous_compact_oriented_singleLinkHeatBathProjection_stronglyMeasurable
      C target ((C).singleLinkHeatBathProjection source O) hSourceStrong
  have hTargetSourceBound :
      ∀ A,
        |(C).singleLinkHeatBathProjection target
          ((C).singleLinkHeatBathProjection source O) A| ≤ M :=
    continuous_compact_oriented_singleLinkHeatBathProjection_abs_le
      C target ((C).singleLinkHeatBathProjection source O)
      hSourceStrong M hM0 hSourceBound
  have hTarget :=
    continuous_compact_oriented_singleLinkHeatBathProjectionL2_toLp_eq
      C target O hOStrong M hM0 hOBound
  have hSource :=
    continuous_compact_oriented_singleLinkHeatBathProjectionL2_toLp_eq
      C source O hOStrong M hM0 hOBound
  have hSourceTarget :=
    continuous_compact_oriented_singleLinkHeatBathProjectionL2_toLp_eq
      C source ((C).singleLinkHeatBathProjection target O)
      hTargetStrong M hM0 hTargetBound
  have hTargetSource :=
    continuous_compact_oriented_singleLinkHeatBathProjectionL2_toLp_eq
      C target ((C).singleLinkHeatBathProjection source O)
      hSourceStrong M hM0 hSourceBound
  unfold ContinuousCompactOrientedGaugeWilsonSystem.gibbsL2RepresentativeBCF
  rw [hTarget, hSource, hSourceTarget, hTargetSource]
  apply Lp.ext
  filter_upwards
    [(continuous_compact_oriented_memLp_two_of_uniform_bound
      C
      ((C).singleLinkHeatBathProjection source
        ((C).singleLinkHeatBathProjection target O))
      hSourceTargetStrong M hM0 hSourceTargetBound).coeFn_toLp,
     (continuous_compact_oriented_memLp_two_of_uniform_bound
      C
      ((C).singleLinkHeatBathProjection target
        ((C).singleLinkHeatBathProjection source O))
      hTargetSourceStrong M hM0 hTargetSourceBound).coeFn_toLp] with A hLeft hRight
  rw [hLeft, hRight]
  exact congrFun
    (periodicHypercubicEvenSpecialUnitary_singleLinkHeatBathProjection_commute_of_sameColor
      H N hN beta hBeta O hNe hColor) A

/-- Distinct one-link heat-bath orthogonal projections of one fixed color
commute on the full Gibbs `L²` Hilbert space. Equality on bounded-continuous
representatives extends by density and continuity. -/
theorem periodicHypercubicEvenSpecialUnitary_singleLinkHeatBathProjectionL2_commute_of_sameColor
    {target source : PeriodicHypercubicEvenEdge H}
    (hNe : source ≠ target)
    (hColor :
      periodicHypercubicEvenEdgeColor H target =
        periodicHypercubicEvenEdgeColor H source)
    (f : L2) :
    (C).singleLinkHeatBathProjectionL2 source
        ((C).singleLinkHeatBathProjectionL2 target f) =
      (C).singleLinkHeatBathProjectionL2 target
        ((C).singleLinkHeatBathProjectionL2 source f) := by
  let p : L2 → Prop := fun q =>
    (C).singleLinkHeatBathProjectionL2 source
        ((C).singleLinkHeatBathProjectionL2 target q) =
      (C).singleLinkHeatBathProjectionL2 target
        ((C).singleLinkHeatBathProjectionL2 source q)
  apply DenseRange.induction_on (p := p)
    (BoundedContinuousFunction.toLp_denseRange
      ℝ (C).gibbsMeasure ℝ (by norm_num)) f
  · apply isClosed_eq
    · exact
        ((C).singleLinkHeatBathProjectionL2 source).continuous.comp
          ((C).singleLinkHeatBathProjectionL2 target).continuous
    · exact
        ((C).singleLinkHeatBathProjectionL2 target).continuous.comp
          ((C).singleLinkHeatBathProjectionL2 source).continuous
  · intro O
    change p
      (BoundedContinuousFunction.toLp 2 (C).gibbsMeasure ℝ O)
    simpa [p,
      ContinuousCompactOrientedGaugeWilsonSystem.gibbsL2RepresentativeBCF] using
      periodicHypercubicEvenSpecialUnitary_singleLinkHeatBathProjectionL2_comm_on_gibbsL2RepresentativeBCF_of_sameColor
        H N hN beta hBeta O hNe hColor

/-- Any two one-link `L²` projections whose links lie in one fixed color class
commute. The equal-link case is tautological; the distinct case is the exact
same-color locality result lifted to the full Gibbs Hilbert space. -/
theorem periodicHypercubicEvenSpecialUnitary_singleLinkHeatBathProjectionL2_pairwise_comm_of_sameColor
    {target source : PeriodicHypercubicEvenEdge H}
    (hColor :
      periodicHypercubicEvenEdgeColor H target =
        periodicHypercubicEvenEdgeColor H source)
    (f : L2) :
    (C).singleLinkHeatBathProjectionL2 source
        ((C).singleLinkHeatBathProjectionL2 target f) =
      (C).singleLinkHeatBathProjectionL2 target
        ((C).singleLinkHeatBathProjectionL2 source f) := by
  by_cases hEq : source = target
  · subst source
    rfl
  · exact
      periodicHypercubicEvenSpecialUnitary_singleLinkHeatBathProjectionL2_commute_of_sameColor
        H N hN beta hBeta hEq hColor f

/-- Ordered finite product of the `L²` one-link projections in one fixed color
class. The head link acts first. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryFixedColorProjectionListL2
    (color : PeriodicHypercubicEvenEdgeColor) :
    List (PeriodicHypercubicEvenFixedColorEdge H color) →
      L2 →L[ℝ] L2
  | [] => ContinuousLinearMap.id ℝ L2
  | e :: es =>
      (periodicHypercubicEvenSpecialUnitaryFixedColorProjectionListL2
        H N hN beta hBeta color es).comp
        ((C).singleLinkHeatBathProjectionL2 e.1)

@[simp] theorem periodicHypercubicEvenSpecialUnitaryFixedColorProjectionListL2_nil_apply
    (color : PeriodicHypercubicEvenEdgeColor)
    (f : L2) :
    periodicHypercubicEvenSpecialUnitaryFixedColorProjectionListL2
      H N hN beta hBeta color [] f = f := by
  rfl

@[simp] theorem periodicHypercubicEvenSpecialUnitaryFixedColorProjectionListL2_cons_apply
    (color : PeriodicHypercubicEvenEdgeColor)
    (e : PeriodicHypercubicEvenFixedColorEdge H color)
    (es : List (PeriodicHypercubicEvenFixedColorEdge H color))
    (f : L2) :
    periodicHypercubicEvenSpecialUnitaryFixedColorProjectionListL2
        H N hN beta hBeta color (e :: es) f =
      periodicHypercubicEvenSpecialUnitaryFixedColorProjectionListL2
        H N hN beta hBeta color es
        ((C).singleLinkHeatBathProjectionL2 e.1 f) := by
  rfl

/-- A fixed-color one-link projection commutes through every finite product of
projections from the same color class. -/
theorem periodicHypercubicEvenSpecialUnitaryFixedColorProjectionListL2_commute
    (color : PeriodicHypercubicEvenEdgeColor)
    (e : PeriodicHypercubicEvenFixedColorEdge H color)
    (es : List (PeriodicHypercubicEvenFixedColorEdge H color))
    (f : L2) :
    (C).singleLinkHeatBathProjectionL2 e.1
        (periodicHypercubicEvenSpecialUnitaryFixedColorProjectionListL2
          H N hN beta hBeta color es f) =
      periodicHypercubicEvenSpecialUnitaryFixedColorProjectionListL2
        H N hN beta hBeta color es
        ((C).singleLinkHeatBathProjectionL2 e.1 f) := by
  induction es generalizing f with
  | nil => rfl
  | cons source rest ih =>
      have hColor :
          periodicHypercubicEvenEdgeColor H source.1 =
            periodicHypercubicEvenEdgeColor H e.1 :=
        source.property.trans e.property.symm
      calc
        (C).singleLinkHeatBathProjectionL2 e.1
            (periodicHypercubicEvenSpecialUnitaryFixedColorProjectionListL2
              H N hN beta hBeta color (source :: rest) f) =
          (C).singleLinkHeatBathProjectionL2 e.1
            (periodicHypercubicEvenSpecialUnitaryFixedColorProjectionListL2
              H N hN beta hBeta color rest
              ((C).singleLinkHeatBathProjectionL2 source.1 f)) := by
            rfl
        _ = periodicHypercubicEvenSpecialUnitaryFixedColorProjectionListL2
              H N hN beta hBeta color rest
              ((C).singleLinkHeatBathProjectionL2 e.1
                ((C).singleLinkHeatBathProjectionL2 source.1 f)) :=
          ih ((C).singleLinkHeatBathProjectionL2 source.1 f)
        _ = periodicHypercubicEvenSpecialUnitaryFixedColorProjectionListL2
              H N hN beta hBeta color rest
              ((C).singleLinkHeatBathProjectionL2 source.1
                ((C).singleLinkHeatBathProjectionL2 e.1 f)) := by
          rw [periodicHypercubicEvenSpecialUnitary_singleLinkHeatBathProjectionL2_pairwise_comm_of_sameColor
            H N hN beta hBeta hColor]
        _ = periodicHypercubicEvenSpecialUnitaryFixedColorProjectionListL2
              H N hN beta hBeta color (source :: rest)
              ((C).singleLinkHeatBathProjectionL2 e.1 f) := by
          rfl

/-- If a link occurs in a fixed-color list, the output of that list product is
fixed by the corresponding one-link `L²` projection. -/
theorem periodicHypercubicEvenSpecialUnitaryFixedColorProjectionListL2_fixed_of_mem
    (color : PeriodicHypercubicEvenEdgeColor)
    (e : PeriodicHypercubicEvenFixedColorEdge H color)
    (es : List (PeriodicHypercubicEvenFixedColorEdge H color))
    (he : e ∈ es)
    (f : L2) :
    (C).singleLinkHeatBathProjectionL2 e.1
        (periodicHypercubicEvenSpecialUnitaryFixedColorProjectionListL2
          H N hN beta hBeta color es f) =
      periodicHypercubicEvenSpecialUnitaryFixedColorProjectionListL2
        H N hN beta hBeta color es f := by
  induction es generalizing f with
  | nil => simp at he
  | cons source rest ih =>
      simp only [List.mem_cons] at he
      rcases he with hEq | hRest
      · subst source
        calc
          (C).singleLinkHeatBathProjectionL2 e.1
              (periodicHypercubicEvenSpecialUnitaryFixedColorProjectionListL2
                H N hN beta hBeta color (e :: rest) f) =
            (C).singleLinkHeatBathProjectionL2 e.1
              (periodicHypercubicEvenSpecialUnitaryFixedColorProjectionListL2
                H N hN beta hBeta color rest
                ((C).singleLinkHeatBathProjectionL2 e.1 f)) := by
              rfl
          _ = periodicHypercubicEvenSpecialUnitaryFixedColorProjectionListL2
                H N hN beta hBeta color rest
                ((C).singleLinkHeatBathProjectionL2 e.1
                  ((C).singleLinkHeatBathProjectionL2 e.1 f)) :=
            periodicHypercubicEvenSpecialUnitaryFixedColorProjectionListL2_commute
              H N hN beta hBeta color e rest
              ((C).singleLinkHeatBathProjectionL2 e.1 f)
          _ = periodicHypercubicEvenSpecialUnitaryFixedColorProjectionListL2
                H N hN beta hBeta color rest
                ((C).singleLinkHeatBathProjectionL2 e.1 f) := by
            rw [continuous_compact_oriented_singleLinkHeatBathProjectionL2_apply_projection]
          _ = periodicHypercubicEvenSpecialUnitaryFixedColorProjectionListL2
                H N hN beta hBeta color (e :: rest) f := by
            rfl
      · exact ih hRest ((C).singleLinkHeatBathProjectionL2 source.1 f)

/-- A fixed-color list product fixes every vector already fixed by all
one-link projections appearing in that list. -/
theorem periodicHypercubicEvenSpecialUnitaryFixedColorProjectionListL2_apply_eq_self_of_forall_mem_fixed
    (color : PeriodicHypercubicEvenEdgeColor)
    (es : List (PeriodicHypercubicEvenFixedColorEdge H color))
    (f : L2)
    (hFixed : ∀ e ∈ es,
      (C).singleLinkHeatBathProjectionL2 e.1 f = f) :
    periodicHypercubicEvenSpecialUnitaryFixedColorProjectionListL2
      H N hN beta hBeta color es f = f := by
  induction es with
  | nil => rfl
  | cons source rest ih =>
      rw [periodicHypercubicEvenSpecialUnitaryFixedColorProjectionListL2_cons_apply,
        hFixed source (by simp)]
      apply ih
      intro e he
      exact hFixed e (by simp [he])

/-- The full common fixed set of all one-link Gibbs `L²` heat-bath projections
inside one canonical color class. -/
def periodicHypercubicEvenSpecialUnitaryFixedColorCommonFixedL2
    (color : PeriodicHypercubicEvenEdgeColor)
    (f : L2) : Prop :=
  ∀ e : PeriodicHypercubicEvenFixedColorEdge H color,
    (C).singleLinkHeatBathProjectionL2 e.1 f = f

/-- Canonical fixed-color heat-bath block on the genuine Gibbs `L²` Hilbert
space: every physical link of one color is projected exactly once. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryFixedColorHeatBathBlockL2
    (color : PeriodicHypercubicEvenEdgeColor) :
    L2 →L[ℝ] L2 :=
  periodicHypercubicEvenSpecialUnitaryFixedColorProjectionListL2
    H N hN beta hBeta color
    ((Finset.univ :
      Finset (PeriodicHypercubicEvenFixedColorEdge H color)).toList)

/-- Every fixed-color `L²` block lands in the common fixed space of all
one-link projections of that color. -/
theorem periodicHypercubicEvenSpecialUnitaryFixedColorHeatBathBlockL2_commonFixed
    (color : PeriodicHypercubicEvenEdgeColor)
    (f : L2) :
    periodicHypercubicEvenSpecialUnitaryFixedColorCommonFixedL2
      H N hN beta hBeta color
      (periodicHypercubicEvenSpecialUnitaryFixedColorHeatBathBlockL2
        H N hN beta hBeta color f) := by
  intro e
  apply
    periodicHypercubicEvenSpecialUnitaryFixedColorProjectionListL2_fixed_of_mem
      H N hN beta hBeta color e
      ((Finset.univ :
        Finset (PeriodicHypercubicEvenFixedColorEdge H color)).toList)
  simp

/-- The fixed-color block fixes every vector already fixed by every one-link
projection in that color class. -/
theorem periodicHypercubicEvenSpecialUnitaryFixedColorHeatBathBlockL2_apply_eq_self_of_commonFixed
    (color : PeriodicHypercubicEvenEdgeColor)
    (f : L2)
    (hFixed : periodicHypercubicEvenSpecialUnitaryFixedColorCommonFixedL2
      H N hN beta hBeta color f) :
    periodicHypercubicEvenSpecialUnitaryFixedColorHeatBathBlockL2
      H N hN beta hBeta color f = f := by
  unfold periodicHypercubicEvenSpecialUnitaryFixedColorHeatBathBlockL2
  apply
    periodicHypercubicEvenSpecialUnitaryFixedColorProjectionListL2_apply_eq_self_of_forall_mem_fixed
      H N hN beta hBeta color
  intro e _he
  exact hFixed e

/-- Fixedness under the canonical fixed-color block is exactly simultaneous
fixedness under every one-link projection of that color. -/
theorem periodicHypercubicEvenSpecialUnitaryFixedColorHeatBathBlockL2_apply_eq_self_iff_commonFixed
    (color : PeriodicHypercubicEvenEdgeColor)
    (f : L2) :
    periodicHypercubicEvenSpecialUnitaryFixedColorHeatBathBlockL2
        H N hN beta hBeta color f = f ↔
      periodicHypercubicEvenSpecialUnitaryFixedColorCommonFixedL2
        H N hN beta hBeta color f := by
  constructor
  · intro hBlock
    have hOutput :=
      periodicHypercubicEvenSpecialUnitaryFixedColorHeatBathBlockL2_commonFixed
        H N hN beta hBeta color f
    intro e
    have he := hOutput e
    rwa [hBlock] at he
  · intro hFixed
    exact
      periodicHypercubicEvenSpecialUnitaryFixedColorHeatBathBlockL2_apply_eq_self_of_commonFixed
        H N hN beta hBeta color f hFixed

/-- The canonical fixed-color Gibbs `L²` heat-bath block is idempotent. -/
theorem periodicHypercubicEvenSpecialUnitaryFixedColorHeatBathBlockL2_idempotent
    (color : PeriodicHypercubicEvenEdgeColor) :
    (periodicHypercubicEvenSpecialUnitaryFixedColorHeatBathBlockL2
      H N hN beta hBeta color).comp
      (periodicHypercubicEvenSpecialUnitaryFixedColorHeatBathBlockL2
        H N hN beta hBeta color) =
    periodicHypercubicEvenSpecialUnitaryFixedColorHeatBathBlockL2
      H N hN beta hBeta color := by
  apply ContinuousLinearMap.ext
  intro f
  rw [ContinuousLinearMap.comp_apply]
  exact
    periodicHypercubicEvenSpecialUnitaryFixedColorHeatBathBlockL2_apply_eq_self_of_commonFixed
      H N hN beta hBeta color
      (periodicHypercubicEvenSpecialUnitaryFixedColorHeatBathBlockL2
        H N hN beta hBeta color f)
      (periodicHypercubicEvenSpecialUnitaryFixedColorHeatBathBlockL2_commonFixed
        H N hN beta hBeta color f)

/-- Every finite fixed-color list product is self-adjoint in the Gibbs `L²`
pairing. The induction uses one-link self-adjointness together with exact
same-color commutation through the remaining product. -/
theorem periodicHypercubicEvenSpecialUnitaryFixedColorProjectionListL2_inner_symm
    (color : PeriodicHypercubicEvenEdgeColor)
    (es : List (PeriodicHypercubicEvenFixedColorEdge H color))
    (f g : L2) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryFixedColorProjectionListL2
          H N hN beta hBeta color es f) g =
      inner ℝ f
        (periodicHypercubicEvenSpecialUnitaryFixedColorProjectionListL2
          H N hN beta hBeta color es g) := by
  induction es generalizing f g with
  | nil => rfl
  | cons source rest ih =>
      calc
        inner ℝ
            (periodicHypercubicEvenSpecialUnitaryFixedColorProjectionListL2
              H N hN beta hBeta color (source :: rest) f) g =
          inner ℝ
            (periodicHypercubicEvenSpecialUnitaryFixedColorProjectionListL2
              H N hN beta hBeta color rest
              ((C).singleLinkHeatBathProjectionL2 source.1 f)) g := by
            rfl
        _ = inner ℝ
              ((C).singleLinkHeatBathProjectionL2 source.1 f)
              (periodicHypercubicEvenSpecialUnitaryFixedColorProjectionListL2
                H N hN beta hBeta color rest g) :=
          ih ((C).singleLinkHeatBathProjectionL2 source.1 f) g
        _ = inner ℝ f
              ((C).singleLinkHeatBathProjectionL2 source.1
                (periodicHypercubicEvenSpecialUnitaryFixedColorProjectionListL2
                  H N hN beta hBeta color rest g)) :=
          continuous_compact_oriented_singleLinkHeatBathProjectionL2_inner_symm
            C source.1 f
            (periodicHypercubicEvenSpecialUnitaryFixedColorProjectionListL2
              H N hN beta hBeta color rest g)
        _ = inner ℝ f
              (periodicHypercubicEvenSpecialUnitaryFixedColorProjectionListL2
                H N hN beta hBeta color rest
                ((C).singleLinkHeatBathProjectionL2 source.1 g)) := by
          rw [periodicHypercubicEvenSpecialUnitaryFixedColorProjectionListL2_commute
            H N hN beta hBeta color source rest g]
        _ = inner ℝ f
              (periodicHypercubicEvenSpecialUnitaryFixedColorProjectionListL2
                H N hN beta hBeta color (source :: rest) g) := by
          rfl

/-- The canonical fixed-color Gibbs `L²` heat-bath block is self-adjoint. -/
theorem periodicHypercubicEvenSpecialUnitaryFixedColorHeatBathBlockL2_inner_symm
    (color : PeriodicHypercubicEvenEdgeColor)
    (f g : L2) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryFixedColorHeatBathBlockL2
          H N hN beta hBeta color f) g =
      inner ℝ f
        (periodicHypercubicEvenSpecialUnitaryFixedColorHeatBathBlockL2
          H N hN beta hBeta color g) := by
  unfold periodicHypercubicEvenSpecialUnitaryFixedColorHeatBathBlockL2
  exact
    periodicHypercubicEvenSpecialUnitaryFixedColorProjectionListL2_inner_symm
      H N hN beta hBeta color
      ((Finset.univ :
        Finset (PeriodicHypercubicEvenFixedColorEdge H color)).toList) f g

/-- The eight canonical color blocks packaged as a finite family of continuous
linear endomorphisms of the genuine Wilson Gibbs `L²` Hilbert space. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryEightColorHeatBathBlockL2
    (color : PeriodicHypercubicEvenEdgeColor) :
    L2 →L[ℝ] L2 :=
  periodicHypercubicEvenSpecialUnitaryFixedColorHeatBathBlockL2
    H N hN beta hBeta color

/-- Every member of the canonical eight-color Gibbs `L²` block family is
idempotent. -/
theorem periodicHypercubicEvenSpecialUnitaryEightColorHeatBathBlockL2_idempotent
    (color : PeriodicHypercubicEvenEdgeColor) :
    (periodicHypercubicEvenSpecialUnitaryEightColorHeatBathBlockL2
      H N hN beta hBeta color).comp
      (periodicHypercubicEvenSpecialUnitaryEightColorHeatBathBlockL2
        H N hN beta hBeta color) =
    periodicHypercubicEvenSpecialUnitaryEightColorHeatBathBlockL2
      H N hN beta hBeta color :=
  periodicHypercubicEvenSpecialUnitaryFixedColorHeatBathBlockL2_idempotent
    H N hN beta hBeta color

/-- Every member of the canonical eight-color Gibbs `L²` block family is
self-adjoint. -/
theorem periodicHypercubicEvenSpecialUnitaryEightColorHeatBathBlockL2_inner_symm
    (color : PeriodicHypercubicEvenEdgeColor)
    (f g : L2) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryEightColorHeatBathBlockL2
          H N hN beta hBeta color f) g =
      inner ℝ f
        (periodicHypercubicEvenSpecialUnitaryEightColorHeatBathBlockL2
          H N hN beta hBeta color g) :=
  periodicHypercubicEvenSpecialUnitaryFixedColorHeatBathBlockL2_inner_symm
    H N hN beta hBeta color f g

end FixedColorL2

end

end MathlibAnalytic
end MGAP4D
