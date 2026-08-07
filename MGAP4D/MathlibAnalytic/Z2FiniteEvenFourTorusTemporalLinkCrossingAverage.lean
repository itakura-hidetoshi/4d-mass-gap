import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeEmbeddingScaleGlobal
import MGAP4D.MathlibAnalytic.FiniteConstantOneKernelNormalization
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusAllVolumeGaugeOrbitWitness
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Every positive spatial unit step moves its base vertex on the finite even
four-torus. -/
theorem finiteEvenFourTorusSpatialVertexStep_ne
    (H : ℕ)
    (v : FiniteEvenFourTorusSpatialVertex H)
    (μ : FiniteEvenFourTorusSpatialDirection) :
    finiteEvenFourTorusSpatialVertexStep H v μ ≠ v := by
  intro h
  have hcoord := congrArg
    (fun w : FiniteEvenFourTorusSpatialVertex H => w.1 μ.1) h
  change
    v.1 μ.1 + (1 : ZMod ((2 * H + 1) + 1)) = v.1 μ.1 at hcoord
  have hone : (1 : ZMod ((2 * H + 1) + 1)) = 0 := by
    apply add_left_cancel (a := v.1 μ.1)
    simpa using hcoord
  exact finiteEvenFourTorusSpatialModulus_one_ne_zero H hone

/-- Endpoint difference of a temporal-link field along one spatial edge. -/
def finiteEvenFourTorusZ2TemporalEdgeDifferenceHom
    (H : ℕ)
    (e : FiniteEvenFourTorusSpatialLink H) :
    FiniteEvenFourTorusZ2TemporalLinkField H →* Z2Gauge where
  toFun U :=
    U e.1 *
      (U (finiteEvenFourTorusSpatialVertexStep H e.1 e.2))⁻¹
  map_one' := by simp
  map_mul' := by
    intro U V
    simp [mul_assoc, mul_comm, mul_left_comm]

/-- The endpoint-difference homomorphism is onto `Z₂`: prescribe the value at
the initial vertex and the identity at the distinct terminal vertex. -/
theorem finiteEvenFourTorusZ2TemporalEdgeDifferenceHom_surjective
    (H : ℕ)
    (e : FiniteEvenFourTorusSpatialLink H) :
    Function.Surjective (finiteEvenFourTorusZ2TemporalEdgeDifferenceHom H e) := by
  intro z
  let U : FiniteEvenFourTorusZ2TemporalLinkField H :=
    fun v => if v = e.1 then z else 1
  refine ⟨U, ?_⟩
  have hstep :
      finiteEvenFourTorusSpatialVertexStep H e.1 e.2 ≠ e.1 :=
    finiteEvenFourTorusSpatialVertexStep_ne H e.1 e.2
  simp [finiteEvenFourTorusZ2TemporalEdgeDifferenceHom, U, hstep]

/-- Local two-level crossing energy as a function of one `Z₂` temporal
plaquette holonomy. -/
def finiteEvenFourTorusZ2CrossingLocalEnergy
    (energyIdentity energyNontrivial : ℝ)
    (g : Z2Gauge) : ℝ :=
  if g = 1 then energyIdentity else energyNontrivial

/-- The unfixed temporal plaquette holonomy factors into a fixed boundary
relative link and the surjective temporal endpoint difference. -/
theorem finiteEvenFourTorusZ2UnfixedTemporalPlaquetteHolonomy_eq_boundary_mul_difference
    (H : ℕ)
    (U : FiniteEvenFourTorusZ2TemporalLinkField H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (e : FiniteEvenFourTorusSpatialLink H) :
    finiteEvenFourTorusZ2UnfixedTemporalPlaquetteHolonomy H U A B e =
      ((A e)⁻¹ * B e) *
        finiteEvenFourTorusZ2TemporalEdgeDifferenceHom H e U := by
  unfold finiteEvenFourTorusZ2UnfixedTemporalPlaquetteHolonomy
    finiteEvenFourTorusZ2TemporalEdgeDifferenceHom
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  ac_rfl

/-- Left multiplication merely permutes the finite `Z₂` carrier, so every
finite sum is invariant under it. -/
theorem z2Gauge_sum_left_mul
    (c : Z2Gauge)
    (w : Z2Gauge → ℝ) :
    (∑ g : Z2Gauge, w (c * g)) = ∑ g : Z2Gauge, w g := by
  let E : Z2Gauge ≃ Z2Gauge :=
    { toFun := fun g => c * g
      invFun := fun g => c⁻¹ * g
      left_inv := by intro g; simp [mul_assoc]
      right_inv := by intro g; simp [mul_assoc] }
  exact Fintype.sum_equiv E _ _ (fun g => by rfl)

/-- At every spatial edge, uniform temporal-link averaging removes all
boundary dependence from the local crossing energy. -/
theorem finiteEvenFourTorusZ2TemporalLinkAverage_localCrossingEnergy_eq
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (A B A' B' : FiniteEvenFourTorusZ2SliceConfiguration H)
    (e : FiniteEvenFourTorusSpatialLink H) :
    (Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) : ℝ)⁻¹ *
        (∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
          finiteEvenFourTorusZ2CrossingLocalEnergy
            energyIdentity energyNontrivial
            (finiteEvenFourTorusZ2UnfixedTemporalPlaquetteHolonomy H U A B e)) =
      (Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) : ℝ)⁻¹ *
        (∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
          finiteEvenFourTorusZ2CrossingLocalEnergy
            energyIdentity energyNontrivial
            (finiteEvenFourTorusZ2UnfixedTemporalPlaquetteHolonomy H U A' B' e)) := by
  rw [show
    (Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) : ℝ)⁻¹ *
        (∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
          finiteEvenFourTorusZ2CrossingLocalEnergy
            energyIdentity energyNontrivial
            (finiteEvenFourTorusZ2UnfixedTemporalPlaquetteHolonomy H U A B e)) =
      (Fintype.card Z2Gauge : ℝ)⁻¹ *
        ∑ g : Z2Gauge,
          finiteEvenFourTorusZ2CrossingLocalEnergy
            energyIdentity energyNontrivial (((A e)⁻¹ * B e) * g) by
    simp_rw [finiteEvenFourTorusZ2UnfixedTemporalPlaquetteHolonomy_eq_boundary_mul_difference]
    exact finiteSurjectiveGroupHom_uniformAverage_comp
      (finiteEvenFourTorusZ2TemporalEdgeDifferenceHom H e)
      (finiteEvenFourTorusZ2TemporalEdgeDifferenceHom_surjective H e)
      (fun g => finiteEvenFourTorusZ2CrossingLocalEnergy
        energyIdentity energyNontrivial (((A e)⁻¹ * B e) * g))]
  rw [z2Gauge_sum_left_mul]
  rw [show
    (Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) : ℝ)⁻¹ *
        (∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
          finiteEvenFourTorusZ2CrossingLocalEnergy
            energyIdentity energyNontrivial
            (finiteEvenFourTorusZ2UnfixedTemporalPlaquetteHolonomy H U A' B' e)) =
      (Fintype.card Z2Gauge : ℝ)⁻¹ *
        ∑ g : Z2Gauge,
          finiteEvenFourTorusZ2CrossingLocalEnergy
            energyIdentity energyNontrivial (((A' e)⁻¹ * B' e) * g) by
    simp_rw [finiteEvenFourTorusZ2UnfixedTemporalPlaquetteHolonomy_eq_boundary_mul_difference]
    exact finiteSurjectiveGroupHom_uniformAverage_comp
      (finiteEvenFourTorusZ2TemporalEdgeDifferenceHom H e)
      (finiteEvenFourTorusZ2TemporalEdgeDifferenceHom_surjective H e)
      (fun g => finiteEvenFourTorusZ2CrossingLocalEnergy
        energyIdentity energyNontrivial (((A' e)⁻¹ * B' e) * g))]
  rw [z2Gauge_sum_left_mul]

/-- The crossing action is the finite sum of its local edge energies. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeCrossingAction_eq_fintype_sum
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (U : FiniteEvenFourTorusZ2TemporalLinkField H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeCrossingAction
        H β energyIdentity energyNontrivial U A B =
      ∑ e : FiniteEvenFourTorusSpatialLink H,
        finiteEvenFourTorusZ2CrossingLocalEnergy
          energyIdentity energyNontrivial
          (finiteEvenFourTorusZ2UnfixedTemporalPlaquetteHolonomy H U A B e) := by
  classical
  unfold finiteEvenFourTorusZ2UnfixedGaugeCrossingAction
    finiteEvenFourTorusZ2CrossingLocalEnergy
  simpa using
    (Finset.sum_toList
      (s := (Finset.univ : Finset (FiniteEvenFourTorusSpatialLink H)))
      (f := fun e : FiniteEvenFourTorusSpatialLink H =>
        if finiteEvenFourTorusZ2UnfixedTemporalPlaquetteHolonomy H U A B e = 1
        then energyIdentity else energyNontrivial)).symm

/-- Uniform averaging of the complete temporal crossing action is independent
of both boundary configurations. -/
theorem finiteEvenFourTorusZ2TemporalLinkAverage_crossingAction_eq
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (A B A' B' : FiniteEvenFourTorusZ2SliceConfiguration H) :
    (Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) : ℝ)⁻¹ *
        (∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
          finiteEvenFourTorusZ2UnfixedGaugeCrossingAction
            H β energyIdentity energyNontrivial U A B) =
      (Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) : ℝ)⁻¹ *
        (∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
          finiteEvenFourTorusZ2UnfixedGaugeCrossingAction
            H β energyIdentity energyNontrivial U A' B') := by
  classical
  simp_rw [finiteEvenFourTorusZ2UnfixedGaugeCrossingAction_eq_fintype_sum]
  rw [Finset.sum_comm, Finset.sum_comm]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _he
  exact finiteEvenFourTorusZ2TemporalLinkAverage_localCrossingEnergy_eq
    H energyIdentity energyNontrivial A B A' B' e

end

end MathlibAnalytic
end MGAP4D