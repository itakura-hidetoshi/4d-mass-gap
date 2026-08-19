import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Order.Real
import Mathlib.Topology.UniformSpace.UniformEmbedding
import Mathlib.Tactic

/-!
# Uniformly continuous extension from nonnegative rational to nonnegative real time

This is the one-dimensional half-line analogue of the existing rational-tuple extension helper.
The canonical inclusion of nonnegative rationals into nonnegative reals is an isometry with dense
range, so every uniformly continuous map into a complete uniform space has a canonical uniformly
continuous extension to `NNReal`.
-/

namespace MGAP4D

noncomputable section

/-- Canonical inclusion of a nonnegative rational into a nonnegative real. -/
def nnratToNNReal (q : NNRat) : NNReal :=
  ⟨((q : ℚ) : ℝ), by exact_mod_cast q.2⟩

@[simp]
theorem nnratToNNReal_coe (q : NNRat) :
    (nnratToNNReal q : ℝ) = ((q : ℚ) : ℝ) :=
  rfl

@[simp]
theorem nnratToNNReal_zero : nnratToNNReal 0 = 0 := by
  apply NNReal.eq
  simp [nnratToNNReal]

@[simp]
theorem nnratToNNReal_add (p q : NNRat) :
    nnratToNNReal (p + q) = nnratToNNReal p + nnratToNNReal q := by
  apply NNReal.eq
  simp [nnratToNNReal]

/-- The half-line rational inclusion preserves distances exactly. -/
theorem nnratToNNReal_isometry : Isometry nnratToNNReal := by
  apply Isometry.of_dist_eq
  intro p q
  change dist (((p : ℚ) : ℝ)) (((q : ℚ) : ℝ)) = dist p q
  rw [Rat.dist_cast]
  exact (NNRat.dist_eq p q).symm

/-- The half-line rational inclusion is uniform inducing. -/
theorem nnratToNNReal_isUniformInducing : IsUniformInducing nnratToNNReal :=
  nnratToNNReal_isometry.isUniformInducing

/-- Nonnegative rational times are dense in nonnegative real time. -/
theorem nnratToNNReal_denseRange : DenseRange nnratToNNReal := by
  apply dense_of_exists_between
  intro a b hab
  have habR : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
  obtain ⟨q, haq, hqb⟩ := exists_rat_btwn habR
  have hq0 : (0 : ℚ) ≤ q := by
    have ha0 : (0 : ℝ) ≤ (a : ℝ) := a.2
    have hq0R : (0 : ℝ) < (q : ℝ) := lt_of_le_of_lt ha0 haq
    exact_mod_cast hq0R.le
  let qn : NNRat := ⟨q, hq0⟩
  refine ⟨nnratToNNReal qn, ⟨qn, rfl⟩, ?_, ?_⟩
  · exact_mod_cast haq
  · exact_mod_cast hqb

/-- Canonical uniformly-extended map from nonnegative rational to nonnegative real time. -/
def nnratUniformlyExtend
    {E : Type*} [UniformSpace E] [T0Space E] [CompleteSpace E]
    (f : NNRat → E) : NNReal → E :=
  (nnratToNNReal_isUniformInducing.isDenseInducing nnratToNNReal_denseRange).extend f

/-- Uniform continuity survives the canonical half-line extension. -/
theorem nnratUniformlyExtend_uniformContinuous
    {E : Type*} [UniformSpace E] [T0Space E] [CompleteSpace E]
    (f : NNRat → E) (hf : UniformContinuous f) :
    UniformContinuous (nnratUniformlyExtend f) := by
  simpa [nnratUniformlyExtend] using
    (uniformContinuous_uniformly_extend
      nnratToNNReal_isUniformInducing nnratToNNReal_denseRange hf)

/-- The canonical half-line extension agrees with the original function at every rational time. -/
theorem nnratUniformlyExtend_nnratToNNReal
    {E : Type*} [UniformSpace E] [T0Space E] [CompleteSpace E]
    (f : NNRat → E) (hf : UniformContinuous f) (q : NNRat) :
    nnratUniformlyExtend f (nnratToNNReal q) = f q := by
  simpa [nnratUniformlyExtend] using
    (uniformly_extend_of_ind
      nnratToNNReal_isUniformInducing nnratToNNReal_denseRange hf q)

/-- The canonical extension is the unique continuous real-half-line function with the prescribed
nonnegative-rational restriction. -/
theorem nnratUniformlyExtend_unique
    {E : Type*} [UniformSpace E] [T0Space E] [CompleteSpace E]
    (f : NNRat → E)
    (g : NNReal → E)
    (hg : ∀ q : NNRat, g (nnratToNNReal q) = f q)
    (hcontinuous : Continuous g) :
    nnratUniformlyExtend f = g := by
  simpa [nnratUniformlyExtend] using
    (uniformly_extend_unique
      nnratToNNReal_isUniformInducing nnratToNNReal_denseRange hg hcontinuous)

end

end MGAP4D
