import MGAP4D.MathlibAnalytic.Z2SinglePlaquetteOSKernel
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Sum of the two local strict-coupling Wilson weights. -/
def z2WilsonTemporalCrossingWeightSum
    (β energyIdentity energyNontrivial : ℝ) : ℝ :=
  z2WilsonWeightIdentity β energyIdentity +
    z2WilsonWeightNontrivial β energyNontrivial

/-- Volume-independent sign-mode contraction rate of the normalized temporal
crossing kernel. -/
def z2WilsonTemporalCrossingRate
    (β energyIdentity energyNontrivial : ℝ) : ℝ :=
  (z2WilsonWeightIdentity β energyIdentity -
      z2WilsonWeightNontrivial β energyNontrivial) /
    z2WilsonTemporalCrossingWeightSum
      β energyIdentity energyNontrivial

/-- Volume-independent Poincare constant dual to the local sign-mode rate. -/
def z2WilsonTemporalCrossingCoercivity
    (β energyIdentity energyNontrivial : ℝ) : ℝ :=
  1 - z2WilsonTemporalCrossingRate
    β energyIdentity energyNontrivial

/-- The nontrivial local Boltzmann weight is strictly smaller at strict
coupling. -/
theorem z2WilsonWeightNontrivial_lt_identity
    {β energyIdentity energyNontrivial : ℝ}
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) :
    z2WilsonWeightNontrivial β energyNontrivial <
      z2WilsonWeightIdentity β energyIdentity := by
  unfold z2WilsonWeightNontrivial z2WilsonWeightIdentity
  apply Real.exp_lt_exp.mpr
  nlinarith

/-- The local Wilson weight sum is strictly positive. -/
theorem z2WilsonTemporalCrossingWeightSum_pos
    (β energyIdentity energyNontrivial : ℝ) :
    0 < z2WilsonTemporalCrossingWeightSum
      β energyIdentity energyNontrivial := by
  unfold z2WilsonTemporalCrossingWeightSum
  exact add_pos
    (z2WilsonWeightIdentity_pos β energyIdentity)
    (z2WilsonWeightNontrivial_pos β energyNontrivial)

/-- Strict coupling gives a strictly positive local sign-mode rate. -/
theorem z2WilsonTemporalCrossingRate_pos
    {β energyIdentity energyNontrivial : ℝ}
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) :
    0 < z2WilsonTemporalCrossingRate
      β energyIdentity energyNontrivial := by
  unfold z2WilsonTemporalCrossingRate
  exact div_pos
    (sub_pos.mpr (z2WilsonWeightNontrivial_lt_identity hβ hEnergy))
    (z2WilsonTemporalCrossingWeightSum_pos
      β energyIdentity energyNontrivial)

/-- Strict coupling gives a local sign-mode rate strictly below one. -/
theorem z2WilsonTemporalCrossingRate_lt_one
    {β energyIdentity energyNontrivial : ℝ}
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) :
    z2WilsonTemporalCrossingRate
        β energyIdentity energyNontrivial < 1 := by
  unfold z2WilsonTemporalCrossingRate
  rw [div_lt_one
    (z2WilsonTemporalCrossingWeightSum_pos
      β energyIdentity energyNontrivial)]
  unfold z2WilsonTemporalCrossingWeightSum
  have hw1 := z2WilsonWeightNontrivial_pos β energyNontrivial
  linarith

/-- Closed formula for the Poincare constant. -/
theorem z2WilsonTemporalCrossingCoercivity_eq
    (β energyIdentity energyNontrivial : ℝ) :
    z2WilsonTemporalCrossingCoercivity
        β energyIdentity energyNontrivial =
      2 * z2WilsonWeightNontrivial β energyNontrivial /
        z2WilsonTemporalCrossingWeightSum
          β energyIdentity energyNontrivial := by
  unfold z2WilsonTemporalCrossingCoercivity
    z2WilsonTemporalCrossingRate
  have hsum :
      z2WilsonTemporalCrossingWeightSum
        β energyIdentity energyNontrivial ≠ 0 :=
    ne_of_gt (z2WilsonTemporalCrossingWeightSum_pos
      β energyIdentity energyNontrivial)
  field_simp [hsum]
  unfold z2WilsonTemporalCrossingWeightSum
  ring

/-- Strict coupling gives a positive volume-independent Poincare constant. -/
theorem z2WilsonTemporalCrossingCoercivity_pos
    {β energyIdentity energyNontrivial : ℝ}
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) :
    0 < z2WilsonTemporalCrossingCoercivity
      β energyIdentity energyNontrivial := by
  unfold z2WilsonTemporalCrossingCoercivity
  linarith [z2WilsonTemporalCrossingRate_lt_one hβ hEnergy]

/-- The Poincare constant is strictly below one at strict coupling. -/
theorem z2WilsonTemporalCrossingCoercivity_lt_one
    {β energyIdentity energyNontrivial : ℝ}
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) :
    z2WilsonTemporalCrossingCoercivity
        β energyIdentity energyNontrivial < 1 := by
  unfold z2WilsonTemporalCrossingCoercivity
  linarith [z2WilsonTemporalCrossingRate_pos hβ hEnergy]

/-- Exact duality of the local crossing rate and coercivity. -/
theorem z2WilsonTemporalCrossingRate_eq_one_sub_coercivity
    (β energyIdentity energyNontrivial : ℝ) :
    z2WilsonTemporalCrossingRate
        β energyIdentity energyNontrivial =
      1 - z2WilsonTemporalCrossingCoercivity
        β energyIdentity energyNontrivial := by
  unfold z2WilsonTemporalCrossingCoercivity
  ring

end

end MathlibAnalytic
end MGAP4D
