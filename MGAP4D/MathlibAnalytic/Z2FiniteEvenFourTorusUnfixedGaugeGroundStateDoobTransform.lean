import MGAP4D.MathlibAnalytic.FiniteStrictlyPositiveKernelGroundStateDoobTransform
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugePerronGroundSimplicity
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators InnerProduct

noncomputable section

/-- A canonical choice of the strictly positive ambient Perron ground vector of
the actual finite-volume unfixed-gauge `Z₂` one-slab transfer. -/
noncomputable def finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2SliceHilbert H :=
  Classical.choose
    (finiteEvenFourTorusZ2UnfixedGaugeAmbient_fixed_space_generated_by_positiveGround
      H β energyIdentity energyNontrivial hβ hEnergy)

/-- The chosen ambient Perron ground is nonzero. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_ne_zero
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
      H β energyIdentity energyNontrivial hβ hEnergy ≠ 0 :=
  (Classical.choose_spec
    (finiteEvenFourTorusZ2UnfixedGaugeAmbient_fixed_space_generated_by_positiveGround
      H β energyIdentity energyNontrivial hβ hEnergy)).1

/-- The chosen ambient Perron ground is pointwise strictly positive. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_pos
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteBoundaryPointwisePositive
      (finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
        H β energyIdentity energyNontrivial hβ hEnergy) :=
  (Classical.choose_spec
    (finiteEvenFourTorusZ2UnfixedGaugeAmbient_fixed_space_generated_by_positiveGround
      H β energyIdentity energyNontrivial hβ hEnergy)).2.1

/-- The chosen ambient Perron ground is fixed by the actual normalized
one-slab transfer. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_fixed
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer
        H β energyIdentity energyNontrivial hβ hEnergy
        (finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
          H β energyIdentity energyNontrivial hβ hEnergy) =
      finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
        H β energyIdentity energyNontrivial hβ hEnergy :=
  (Classical.choose_spec
    (finiteEvenFourTorusZ2UnfixedGaugeAmbient_fixed_space_generated_by_positiveGround
      H β energyIdentity energyNontrivial hβ hEnergy)).2.2.1

/-- The actual unfixed-gauge kernel together with its chosen positive Perron
ground defines an exact reversible ground-state Doob transform. -/
noncomputable def finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteKernelGroundStateDoobData
      (FiniteEvenFourTorusZ2SliceConfiguration H) :=
  { kernel :=
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
        H β energyIdentity energyNontrivial hβ hEnergy
    ground :=
      finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
        H β energyIdentity energyNontrivial hβ hEnergy
    ground_pos :=
      finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_pos
        H β energyIdentity energyNontrivial hβ hEnergy
    ground_fixed :=
      finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_fixed
        H β energyIdentity energyNontrivial hβ hEnergy
    kernel_symmetric :=
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_symmetric
        H β energyIdentity energyNontrivial hβ hEnergy
    kernel_nonneg := fun A B =>
      le_of_lt
        (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_pos
          H β energyIdentity energyNontrivial hβ hEnergy A B)
    raw_ne_zero :=
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer_ne_zero
        H β energyIdentity energyNontrivial hβ hEnergy }

/-- The actual Perron Doob transition kernel. -/
noncomputable def finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobKernel
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2SliceConfiguration H →
      FiniteEvenFourTorusZ2SliceConfiguration H → ℝ :=
  (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
    H β energyIdentity energyNontrivial hβ hEnergy).doobKernel

/-- The actual Perron Doob kernel is row stochastic. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobKernel_sum_eq_one
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    ∑ A : FiniteEvenFourTorusZ2SliceConfiguration H,
      finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobKernel
        H β energyIdentity energyNontrivial hβ hEnergy A B = 1 :=
  (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
    H β energyIdentity energyNontrivial hβ hEnergy).doobKernel_sum_eq_one B

/-- The actual Perron Doob kernel is nonnegative. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobKernel_nonneg
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    0 ≤ finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobKernel
      H β energyIdentity energyNontrivial hβ hEnergy A B :=
  (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
    H β energyIdentity energyNontrivial hβ hEnergy).doobKernel_nonneg A B

/-- Detailed balance holds exactly with reversible density equal to the square
of the actual positive Perron ground. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobKernel_detailedBalance
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    (finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
        H β energyIdentity energyNontrivial hβ hEnergy B) ^ 2 *
        finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobKernel
          H β energyIdentity energyNontrivial hβ hEnergy A B =
      (finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
        H β energyIdentity energyNontrivial hβ hEnergy A) ^ 2 *
        finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobKernel
          H β energyIdentity energyNontrivial hβ hEnergy B A :=
  (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
    H β energyIdentity energyNontrivial hβ hEnergy).doobKernel_detailedBalance A B

/-- Ground multiplication exactly intertwines the actual Perron Doob operator
with the original ambient normalized one-slab transfer. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoob_intertwining
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2SliceHilbert H) :
    (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
        H β energyIdentity energyNontrivial hβ hEnergy).weightedVector
      (finiteKernelOperator
        (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobKernel
          H β energyIdentity energyNontrivial hβ hEnergy) f) =
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer
        H β energyIdentity energyNontrivial hβ hEnergy
        ((finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
          H β energyIdentity energyNontrivial hβ hEnergy).weightedVector f) :=
  (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
    H β energyIdentity energyNontrivial hβ hEnergy).weightedVector_doobOperator f

/-- An actual weighted mean-zero Rayleigh estimate for the Perron Doob chain
implies the corresponding Perron-orthogonal estimate for the compressed
Gauss-invariant one-slab transfer. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeInvariant_transfer_rayleigh_le_of_weightedDoob
    (H : ℕ)
    (β energyIdentity energyNontrivial rate : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (hDoob : ∀ f : FiniteEvenFourTorusZ2SliceHilbert H,
      (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
          H β energyIdentity energyNontrivial hβ hEnergy).weightedMean f = 0 →
        (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
            H β energyIdentity energyNontrivial hβ hEnergy).weightedDoobQuadratic f ≤
          rate *
            (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
              H β energyIdentity energyNontrivial hβ hEnergy).weightedNormSq f)
    (x : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H)
    (hx : inner ℝ x.1
      (finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
        H β energyIdentity energyNontrivial hβ hEnergy) = 0) :
    inner ℝ
        (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
          H β energyIdentity energyNontrivial hβ hEnergy x) x ≤
      rate * ‖x‖ ^ 2 := by
  change inner ℝ
      (finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer
        H β energyIdentity energyNontrivial hβ hEnergy x.1) x.1 ≤
    rate * ‖x.1‖ ^ 2
  exact
    (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
      H β energyIdentity energyNontrivial hβ hEnergy).transfer_rayleigh_le_of_weightedDoob
        rate hDoob x.1 hx

/-- The actual full-transfer centered Rayleigh problem is therefore exactly a
weighted mean-zero Poincare problem for the reversible Perron Doob chain. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeAmbient_transfer_rayleigh_iff_weightedDoob
    (H : ℕ)
    (β energyIdentity energyNontrivial rate : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    (∀ x : FiniteEvenFourTorusZ2SliceHilbert H,
      inner ℝ x
          (finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
            H β energyIdentity energyNontrivial hβ hEnergy) = 0 →
        inner ℝ
            (finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer
              H β energyIdentity energyNontrivial hβ hEnergy x) x ≤
          rate * ‖x‖ ^ 2) ↔
      (∀ f : FiniteEvenFourTorusZ2SliceHilbert H,
        (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
            H β energyIdentity energyNontrivial hβ hEnergy).weightedMean f = 0 →
          (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
              H β energyIdentity energyNontrivial hβ hEnergy).weightedDoobQuadratic f ≤
            rate *
              (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
                H β energyIdentity energyNontrivial hβ hEnergy).weightedNormSq f) :=
  (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
    H β energyIdentity energyNontrivial hβ hEnergy).transfer_rayleigh_iff_weightedDoob rate

end

end MathlibAnalytic
end MGAP4D
