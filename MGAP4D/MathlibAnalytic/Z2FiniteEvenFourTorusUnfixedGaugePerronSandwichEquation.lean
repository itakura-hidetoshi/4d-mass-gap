import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeGroundStateDoobTransform
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusOneSlabSandwichFactorization
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators InnerProduct

noncomputable section

/-- The positive eigenvalue of the raw temporal-link-summed transfer carried by
its normalized Perron ground. -/
def finiteEvenFourTorusZ2UnfixedGaugeRawPerronScale
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) : ℝ :=
  ‖finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer
    H β energyIdentity energyNontrivial hβ hEnergy‖

/-- The raw Perron scale is strictly positive. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeRawPerronScale_pos
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    0 < finiteEvenFourTorusZ2UnfixedGaugeRawPerronScale
      H β energyIdentity energyNontrivial hβ hEnergy := by
  unfold finiteEvenFourTorusZ2UnfixedGaugeRawPerronScale
  exact norm_pos_iff.mpr
    (finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer_ne_zero
      H β energyIdentity energyNontrivial hβ hEnergy)

/-- Undoing operator-norm normalization shows that the chosen positive Perron
ground is an exact eigenvector of the raw temporal-link-summed transfer with
eigenvalue equal to its operator norm. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_raw_eigen
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer
        H β energyIdentity energyNontrivial hβ hEnergy
        (finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
          H β energyIdentity energyNontrivial hβ hEnergy) =
      finiteEvenFourTorusZ2UnfixedGaugeRawPerronScale
          H β energyIdentity energyNontrivial hβ hEnergy •
        finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
          H β energyIdentity energyNontrivial hβ hEnergy := by
  let p := finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
    H β energyIdentity energyNontrivial hβ hEnergy
  let R := finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer
    H β energyIdentity energyNontrivial hβ hEnergy
  have hfix :=
    finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_fixed
      H β energyIdentity energyNontrivial hβ hEnergy
  have hfixRaw : ‖R‖⁻¹ • R p = p := by
    simpa [p, R,
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer,
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer,
      finiteKernelNormalizedOperator] using hfix
  have hnorm : 0 < ‖R‖ := by
    exact norm_pos_iff.mpr
      (finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer_ne_zero
        H β energyIdentity energyNontrivial hβ hEnergy)
  ext A
  have hpoint := congrArg (fun f : FiniteEvenFourTorusZ2SliceHilbert H => f A) hfixRaw
  change ‖R‖⁻¹ * (R p) A = p A at hpoint
  change (R p) A = ‖R‖ * p A
  calc
    (R p) A = ‖R‖ * (‖R‖⁻¹ * (R p) A) := by
      field_simp [ne_of_gt hnorm]
    _ = ‖R‖ * p A := by rw [hpoint]

/-- The Perron ground is Gauss invariant, so the raw temporal-gauge transfer
acts on it exactly as the temporal-link-summed raw transfer does. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_temporalGaugeRaw_eigen
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer
        H β energyIdentity energyNontrivial hβ hEnergy
        (finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
          H β energyIdentity energyNontrivial hβ hEnergy) =
      finiteEvenFourTorusZ2UnfixedGaugeRawPerronScale
          H β energyIdentity energyNontrivial hβ hEnergy •
        finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
          H β energyIdentity energyNontrivial hβ hEnergy := by
  let p := finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
    H β energyIdentity energyNontrivial hβ hEnergy
  let q : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H :=
    ⟨p,
      finiteEvenFourTorusZ2UnfixedGauge_fixedVector_mem_invariant
        H β energyIdentity energyNontrivial hβ hEnergy p
        (finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_fixed
          H β energyIdentity energyNontrivial hβ hEnergy)⟩
  calc
    finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer
        H β energyIdentity energyNontrivial hβ hEnergy p =
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer
        H β energyIdentity energyNontrivial hβ hEnergy p := by
          symm
          simpa [q] using
            finiteEvenFourTorusZ2UnfixedGaugeRawTransfer_apply_invariant
              H β energyIdentity energyNontrivial hβ hEnergy q
    _ = finiteEvenFourTorusZ2UnfixedGaugeRawPerronScale
          H β energyIdentity energyNontrivial hβ hEnergy • p :=
      finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_raw_eigen
        H β energyIdentity energyNontrivial hβ hEnergy

/-- Exact operator form of the Perron self-consistency equation after splitting
the one-slab transfer into the spatial half-weight sandwich around the
normalized temporal crossing Markov operator. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_crossingSandwich_eigen
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2TemporalCrossingScale
        H β energyIdentity energyNontrivial •
      ((finiteEvenFourTorusZ2SpatialHalfWeightMultiplicationOperator
          H β energyIdentity energyNontrivial).comp
        ((finiteKernelOperator
          (finiteEvenFourTorusZ2NormalizedTemporalCrossingKernel
            H β energyIdentity energyNontrivial)).comp
          (finiteEvenFourTorusZ2SpatialHalfWeightMultiplicationOperator
            H β energyIdentity energyNontrivial)))
        (finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
          H β energyIdentity energyNontrivial hβ hEnergy) =
      finiteEvenFourTorusZ2UnfixedGaugeRawPerronScale
          H β energyIdentity energyNontrivial hβ hEnergy •
        finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
          H β energyIdentity energyNontrivial hβ hEnergy := by
  have h :=
    finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_temporalGaugeRaw_eigen
      H β energyIdentity energyNontrivial hβ hEnergy
  rw [finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer_eq_crossingScale_smul
    H β energyIdentity energyNontrivial hβ hEnergy] at h
  exact h

/-- Componentwise Perron fixed-point equation.  It displays explicitly the
spatial Wilson half-weight, the product temporal crossing smoother, and the
unknown positive Perron factor that must be controlled by the remaining
high-temperature argument. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_crossingSandwich_apply
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2TemporalCrossingScale
          H β energyIdentity energyNontrivial *
        (finiteEvenFourTorusZ2SpatialHalfWeight
            H β energyIdentity energyNontrivial B *
          finiteKernelOperator
              (finiteEvenFourTorusZ2NormalizedTemporalCrossingKernel
                H β energyIdentity energyNontrivial)
              (finiteEvenFourTorusZ2SpatialHalfWeightMultiplicationOperator
                H β energyIdentity energyNontrivial
                (finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
                  H β energyIdentity energyNontrivial hβ hEnergy)) B) =
      finiteEvenFourTorusZ2UnfixedGaugeRawPerronScale
          H β energyIdentity energyNontrivial hβ hEnergy *
        finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
          H β energyIdentity energyNontrivial hβ hEnergy B := by
  have h := congrArg
    (fun f : FiniteEvenFourTorusZ2SliceHilbert H => f B)
    (finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_crossingSandwich_eigen
      H β energyIdentity energyNontrivial hβ hEnergy)
  simpa using h

end

end MathlibAnalytic
end MGAP4D
