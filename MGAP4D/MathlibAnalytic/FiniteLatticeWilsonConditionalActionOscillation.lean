import MGAP4D.MathlibAnalytic.FiniteNormalizedExponentialOscillation
import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonConditionalLocalFactor
import MGAP4D.MathlibAnalytic.FiniteWilsonActiveConditionalExpRatioFamilyGap

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal

noncomputable section

/-- Real log-weight of the exact target-local Wilson conditional factor. -/
def FiniteLatticeWilsonSystem.targetLocalSingleLinkLogWeight
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge)
    (u : L.Gauge) : ℝ :=
  -L.beta *
    L.targetLocalPlaquetteAction (L.replaceLink A target u) target

/-- The real value of the finite target-local partition function is the finite
sum of the corresponding real exponential log-weights. -/
theorem finite_lattice_targetLocalSingleLinkPartitionFunction_toReal
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge) :
    (L.targetLocalSingleLinkPartitionFunction A target).toReal =
      finiteExpPartition (L.targetLocalSingleLinkLogWeight A target) := by
  classical
  unfold FiniteLatticeWilsonSystem.targetLocalSingleLinkPartitionFunction
    finiteExpPartition
  rw [tsum_fintype]
  calc
    ENNReal.toReal
        (∑ u : L.Gauge,
          L.targetLocalSingleLinkBoltzmannWeight A target u) =
      ∑ u : L.Gauge,
        (L.targetLocalSingleLinkBoltzmannWeight A target u).toReal := by
          exact ENNReal.toReal_sum
            (fun u _hu => by
              simp [FiniteLatticeWilsonSystem.targetLocalSingleLinkBoltzmannWeight])
    _ = ∑ u : L.Gauge,
        Real.exp (L.targetLocalSingleLinkLogWeight A target u) := by
      apply Finset.sum_congr rfl
      intro u _hu
      simp [FiniteLatticeWilsonSystem.targetLocalSingleLinkBoltzmannWeight,
        FiniteLatticeWilsonSystem.targetLocalSingleLinkLogWeight]

/-- The exact Wilson single-link conditional PMF, after cancellation of the
remote factor, is the normalized real exponential of the target-local
log-weight. -/
theorem finite_lattice_singleLinkConditionalPMF_toReal_eq_finiteNormalizedExp
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge)
    (u : L.Gauge) :
    (L.singleLinkConditionalPMF A target u).toReal =
      finiteNormalizedExp (L.targetLocalSingleLinkLogWeight A target) u := by
  rw [finite_lattice_singleLinkConditionalPMF_eq_targetLocal,
    finite_lattice_targetLocalSingleLinkConditionalPMF_apply]
  unfold finiteNormalizedExp
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv,
    finite_lattice_targetLocalSingleLinkPartitionFunction_toReal]
  simp [FiniteLatticeWilsonSystem.targetLocalSingleLinkBoltzmannWeight,
    FiniteLatticeWilsonSystem.targetLocalSingleLinkLogWeight,
    div_eq_mul_inv]

/-- Uniform oscillation control of the target-local action difference produced
by every active source-link perturbation. -/
def FiniteLatticeWilsonSystem.ActiveLocalActionDifferenceOscillationBound
    (L : FiniteLatticeWilsonSystem)
    (omega : ℝ) : Prop :=
  ∀ (target source : L.Edge) (A : L.Configuration) (g : L.Gauge),
    source ∈ L.activePlaquetteNeighbors target →
      ∀ u v : L.Gauge,
        ((L.targetLocalPlaquetteAction
              (L.replaceLink A target u) target -
            L.targetLocalPlaquetteAction
              (L.replaceLink (L.replaceLink A source g) target u) target) -
          (L.targetLocalPlaquetteAction
              (L.replaceLink A target v) target -
            L.targetLocalPlaquetteAction
              (L.replaceLink (L.replaceLink A source g) target v) target)) ≤
        omega

/-- A target-local action-difference oscillation bound `omega` gives the exact
conditional likelihood-ratio radius `beta * omega` after normalization. -/
theorem finite_lattice_activeConditionalExpRatioBound_of_localActionOscillation
    (L : FiniteLatticeWilsonSystem)
    (omega : ℝ)
    (hOmega : 0 ≤ omega)
    (hOsc : L.ActiveLocalActionDifferenceOscillationBound omega) :
    L.ActiveConditionalExpRatioBound (L.beta * omega) := by
  intro target source A g hActive u
  let logA : L.Gauge → ℝ :=
    L.targetLocalSingleLinkLogWeight A target
  let logB : L.Gauge → ℝ :=
    L.targetLocalSingleLinkLogWeight (L.replaceLink A source g) target
  have hLogOsc : ∀ x y : L.Gauge,
      (logA x - logB x) - (logA y - logB y) ≤ L.beta * omega := by
    intro x y
    have hAction := hOsc target source A g hActive y x
    have hMul := mul_le_mul_of_nonneg_left hAction L.beta_nonneg
    dsimp [logA, logB,
      FiniteLatticeWilsonSystem.targetLocalSingleLinkLogWeight]
    nlinarith
  have hRatio :=
    finiteNormalizedExp_mutual_le_exp_mul_of_difference_oscillation_all
      logA logB (L.beta * omega) hLogOsc u
  rw [finite_lattice_singleLinkConditionalPMF_toReal_eq_finiteNormalizedExp,
    finite_lattice_singleLinkConditionalPMF_toReal_eq_finiteNormalizedExp]
  exact hRatio

/-- An absolute bound on every target-local action difference gives the coarser
conditional likelihood-ratio radius `2 * beta * delta`. -/
theorem finite_lattice_activeConditionalExpRatioBound_of_abs_localActionDifference
    (L : FiniteLatticeWilsonSystem)
    (delta : ℝ)
    (hDelta : 0 ≤ delta)
    (hAbs : ∀ (target source : L.Edge) (A : L.Configuration) (g : L.Gauge),
      source ∈ L.activePlaquetteNeighbors target →
        ∀ u : L.Gauge,
          |L.targetLocalPlaquetteAction
                (L.replaceLink A target u) target -
            L.targetLocalPlaquetteAction
                (L.replaceLink (L.replaceLink A source g) target u) target| ≤
          delta) :
    L.ActiveConditionalExpRatioBound (2 * L.beta * delta) := by
  have hOsc :
      L.ActiveLocalActionDifferenceOscillationBound (2 * delta) := by
    intro target source A g hActive u v
    have hu := abs_le.mp (hAbs target source A g hActive u)
    have hv := abs_le.mp (hAbs target source A g hActive v)
    linarith
  have h :=
    finite_lattice_activeConditionalExpRatioBound_of_localActionOscillation
      L (2 * delta) (by positivity) hOsc
  simpa [mul_assoc, mul_left_comm, mul_comm] using h

/-- Family-level input expressed directly as a scale-dependent target-local
action-difference oscillation estimate. -/
structure FiniteWilsonActiveLocalActionOscillationFamilyData
    (W : FiniteWilsonOSAutomaticApproximationFamily) where
  edgeCard_pos : ∀ i : W.index, 0 < Fintype.card (W.system i).Edge
  activeDegree_pos : ∀ i : W.index,
    0 < (W.system i).canonicalActivePlaquetteDegree (edgeCard_pos i)
  actionOscillation : W.index → ℝ
  actionOscillation_nonneg : ∀ i : W.index, 0 ≤ actionOscillation i
  activeLocalActionOscillationBound : ∀ i : W.index,
    (W.system i).ActiveLocalActionDifferenceOscillationBound
      (actionOscillation i)
  normalizedExpTV_lt_inv_activeDegree : ∀ i : W.index,
    (Real.exp ((W.system i).beta * actionOscillation i) - 1) /
        (Real.exp ((W.system i).beta * actionOscillation i) + 1) <
      ((W.system i).canonicalActivePlaquetteDegree (edgeCard_pos i) : ℝ)⁻¹

/-- Convert local action oscillation estimates into the active conditional
exponential-ratio package consumed by the finite-volume gap spine. -/
noncomputable def
    FiniteWilsonActiveLocalActionOscillationFamilyData.toConditionalExpRatioFamilyData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonActiveLocalActionOscillationFamilyData W) :
    FiniteWilsonActiveConditionalExpRatioFamilyData W :=
  { edgeCard_pos := D.edgeCard_pos
    activeDegree_pos := D.activeDegree_pos
    radius := fun i => (W.system i).beta * D.actionOscillation i
    radius_nonneg := fun i =>
      mul_nonneg (W.system i).beta_nonneg (D.actionOscillation_nonneg i)
    activeConditionalExpRatioBound := fun i =>
      finite_lattice_activeConditionalExpRatioBound_of_localActionOscillation
        (W.system i) (D.actionOscillation i)
          (D.actionOscillation_nonneg i)
          (D.activeLocalActionOscillationBound i)
    expRatioTV_lt_inv_activeDegree :=
      D.normalizedExpTV_lt_inv_activeDegree }

/-- Local action oscillation estimates generate normalized Hamiltonian gap data
at every finite Wilson scale. -/
noncomputable def
    FiniteWilsonActiveLocalActionOscillationFamilyData.hamiltonianGapData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonActiveLocalActionOscillationFamilyData W)
    (i : W.index) :
    FiniteWilsonVacuumOrthogonalDerivedInvarianceGapData :=
  D.toConditionalExpRatioFamilyData.hamiltonianGapData i

/-- The target-local action oscillation criterion yields normalized Hamiltonian
exact-gap coercivity on every finite-volume vacuum-orthogonal sector. -/
theorem finite_wilson_active_local_action_oscillation_family_hamiltonian_gap
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (D : FiniteWilsonActiveLocalActionOscillationFamilyData W)
    (i : W.index)
    (x : (W.system i).GibbsHilbertSpace)
    (hx : x ∈ finiteVacuumOrthogonal (W.system i).gibbsHilbertVacuum) :
    exactGapValueReal * ‖x‖ ^ 2 ≤
      inner ℝ
        ((W.system i).gibbsDobrushinScaledHeatBathHamiltonianLinearMap
          (D.toConditionalExpRatioFamilyData.toReciprocalInfluenceFamilyData
            .toProductFamilyData.rayleighFamilyData.atScale i) x) x :=
  finite_wilson_active_conditional_exp_ratio_family_hamiltonian_gap
    W D.toConditionalExpRatioFamilyData i x hx

/-- Every excitation-sector eigenvalue generated from local action oscillation
is bounded below by the public exact gap. -/
theorem finite_wilson_active_local_action_oscillation_family_restricted_eigenvalues_ge_exactGap
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (D : FiniteWilsonActiveLocalActionOscillationFamilyData W)
    (i : W.index)
    (j : Fin (D.hamiltonianGapData i).ExcitedDimension) :
    exactGapValueReal ≤
      (finite_wilson_vacuum_orthogonal_restricted_hamiltonian_symmetric
        (D.hamiltonianGapData i).toVacuumOrthogonalGapData 0).eigenvalues
          (D.hamiltonianGapData i).excitedFinrank j :=
  finite_wilson_active_conditional_exp_ratio_family_restricted_eigenvalues_ge_exactGap
    W D.toConditionalExpRatioFamilyData i j

end

end MathlibAnalytic
end MGAP4D
