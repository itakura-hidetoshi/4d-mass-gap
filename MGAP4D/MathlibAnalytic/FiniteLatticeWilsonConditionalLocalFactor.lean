import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonActionLocalDecomposition

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal

noncomputable section

/-- The target-local factor in a single-link Wilson Boltzmann weight. -/
def FiniteLatticeWilsonSystem.targetLocalSingleLinkBoltzmannWeight
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge)
    (g : L.Gauge) : ℝ≥0∞ :=
  ENNReal.ofReal
    (Real.exp
      (-L.beta *
        L.targetLocalPlaquetteAction (L.replaceLink A target g) target))

/-- The target-remote positive factor common to every possible value inserted
at the selected target link. -/
def FiniteLatticeWilsonSystem.targetRemoteBoltzmannFactor
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge) : ℝ≥0∞ :=
  ENNReal.ofReal
    (Real.exp (-L.beta * L.targetRemotePlaquetteAction A target))

/-- The local Boltzmann factor is strictly positive. -/
theorem finite_lattice_targetLocalSingleLinkBoltzmannWeight_pos
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge)
    (g : L.Gauge) :
    0 < L.targetLocalSingleLinkBoltzmannWeight A target g := by
  rw [FiniteLatticeWilsonSystem.targetLocalSingleLinkBoltzmannWeight,
    ENNReal.ofReal_pos]
  exact Real.exp_pos _

/-- The remote Boltzmann factor is strictly positive. -/
theorem finite_lattice_targetRemoteBoltzmannFactor_pos
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge) :
    0 < L.targetRemoteBoltzmannFactor A target := by
  rw [FiniteLatticeWilsonSystem.targetRemoteBoltzmannFactor,
    ENNReal.ofReal_pos]
  exact Real.exp_pos _

/-- The remote Boltzmann factor is nonzero. -/
theorem finite_lattice_targetRemoteBoltzmannFactor_ne_zero
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge) :
    L.targetRemoteBoltzmannFactor A target ≠ 0 :=
  ne_of_gt (finite_lattice_targetRemoteBoltzmannFactor_pos L A target)

/-- The remote Boltzmann factor is finite. -/
theorem finite_lattice_targetRemoteBoltzmannFactor_ne_top
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge) :
    L.targetRemoteBoltzmannFactor A target ≠ ∞ := by
  simp [FiniteLatticeWilsonSystem.targetRemoteBoltzmannFactor]

/-- Every exact single-link Boltzmann weight factors into its target-local part
and a target-value-independent remote factor. -/
theorem finite_lattice_singleLinkBoltzmannWeight_eq_local_mul_remote
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge)
    (g : L.Gauge) :
    L.singleLinkBoltzmannWeight A target g =
      L.targetLocalSingleLinkBoltzmannWeight A target g *
        L.targetRemoteBoltzmannFactor A target := by
  unfold FiniteLatticeWilsonSystem.singleLinkBoltzmannWeight
    FiniteLatticeWilsonSystem.boltzmannWeight
    FiniteLatticeWilsonSystem.targetLocalSingleLinkBoltzmannWeight
    FiniteLatticeWilsonSystem.targetRemoteBoltzmannFactor
  rw [finite_lattice_wilsonAction_replaceLink_eq_local_add_remote]
  have hArg :
      -L.beta *
          (L.targetLocalPlaquetteAction
              (L.replaceLink A target g) target +
            L.targetRemotePlaquetteAction A target) =
        -L.beta *
            L.targetLocalPlaquetteAction
              (L.replaceLink A target g) target +
          -L.beta * L.targetRemotePlaquetteAction A target := by
    ring
  rw [hArg, Real.exp_add,
    ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _))]

/-- The partition function of the target-local factors. -/
def FiniteLatticeWilsonSystem.targetLocalSingleLinkPartitionFunction
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge) : ℝ≥0∞ :=
  ∑' g : L.Gauge, L.targetLocalSingleLinkBoltzmannWeight A target g

/-- The local single-link partition function is nonzero. -/
theorem finite_lattice_targetLocalSingleLinkPartitionFunction_ne_zero
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge) :
    L.targetLocalSingleLinkPartitionFunction A target ≠ 0 := by
  intro hZero
  have hAll :
      ∀ g : L.Gauge,
        L.targetLocalSingleLinkBoltzmannWeight A target g = 0 := by
    simpa [FiniteLatticeWilsonSystem.targetLocalSingleLinkPartitionFunction] using
      (ENNReal.tsum_eq_zero.mp hZero)
  exact
    (ne_of_gt
      (finite_lattice_targetLocalSingleLinkBoltzmannWeight_pos
        L A target default))
      (hAll default)

/-- The local single-link partition function is finite. -/
theorem finite_lattice_targetLocalSingleLinkPartitionFunction_ne_top
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge) :
    L.targetLocalSingleLinkPartitionFunction A target ≠ ∞ := by
  classical
  unfold FiniteLatticeWilsonSystem.targetLocalSingleLinkPartitionFunction
  rw [tsum_fintype]
  exact ENNReal.sum_ne_top.2 fun g _hg => by
    simp [FiniteLatticeWilsonSystem.targetLocalSingleLinkBoltzmannWeight]

/-- The full single-link partition function carries the same common remote
factor as every individual conditional Boltzmann weight. -/
theorem finite_lattice_singleLinkPartitionFunction_eq_local_mul_remote
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge) :
    L.singleLinkPartitionFunction A target =
      L.targetLocalSingleLinkPartitionFunction A target *
        L.targetRemoteBoltzmannFactor A target := by
  classical
  unfold FiniteLatticeWilsonSystem.singleLinkPartitionFunction
    FiniteLatticeWilsonSystem.targetLocalSingleLinkPartitionFunction
  rw [tsum_fintype, tsum_fintype]
  simp_rw [finite_lattice_singleLinkBoltzmannWeight_eq_local_mul_remote]
  exact (Finset.sum_mul _ _ _).symm

/-- The normalized PMF made only from target-local factors. -/
def FiniteLatticeWilsonSystem.targetLocalSingleLinkConditionalPMF
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge) : PMF L.Gauge :=
  PMF.normalize (L.targetLocalSingleLinkBoltzmannWeight A target)
    (finite_lattice_targetLocalSingleLinkPartitionFunction_ne_zero
      L A target)
    (finite_lattice_targetLocalSingleLinkPartitionFunction_ne_top
      L A target)

/-- Pointwise formula for the normalized target-local conditional law. -/
theorem finite_lattice_targetLocalSingleLinkConditionalPMF_apply
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge)
    (g : L.Gauge) :
    L.targetLocalSingleLinkConditionalPMF A target g =
      L.targetLocalSingleLinkBoltzmannWeight A target g *
        (L.targetLocalSingleLinkPartitionFunction A target)⁻¹ := by
  rfl

/-- The target-remote common factor cancels exactly from the normalized
single-link conditional Gibbs law. -/
theorem finite_lattice_singleLinkConditionalPMF_eq_targetLocal
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge) :
    L.singleLinkConditionalPMF A target =
      L.targetLocalSingleLinkConditionalPMF A target := by
  ext g
  rw [finite_lattice_singleLinkConditionalPMF_apply,
    finite_lattice_targetLocalSingleLinkConditionalPMF_apply,
    finite_lattice_singleLinkBoltzmannWeight_eq_local_mul_remote,
    finite_lattice_singleLinkPartitionFunction_eq_local_mul_remote]
  let z := L.targetLocalSingleLinkPartitionFunction A target
  let r := L.targetRemoteBoltzmannFactor A target
  have hr0 : r ≠ 0 := by
    exact finite_lattice_targetRemoteBoltzmannFactor_ne_zero L A target
  have hrt : r ≠ ∞ := by
    exact finite_lattice_targetRemoteBoltzmannFactor_ne_top L A target
  change
    (L.targetLocalSingleLinkBoltzmannWeight A target g * r) *
        (z * r)⁻¹ =
      L.targetLocalSingleLinkBoltzmannWeight A target g * z⁻¹
  calc
    (L.targetLocalSingleLinkBoltzmannWeight A target g * r) *
          (z * r)⁻¹ =
        (L.targetLocalSingleLinkBoltzmannWeight A target g * z⁻¹) *
          (r * r⁻¹) := by
      rw [ENNReal.mul_inv (Or.inr hrt) (Or.inr hr0)]
      ac_rfl
    _ = L.targetLocalSingleLinkBoltzmannWeight A target g * z⁻¹ := by
      rw [ENNReal.mul_inv_cancel hr0 hrt, mul_one]

end

end MathlibAnalytic
end MGAP4D
