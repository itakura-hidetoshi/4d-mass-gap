import MGAP4D.MathlibAnalytic.FiniteDimensionalSymmetricSelectedEigenbasisSpectralWitness
import MGAP4D.MathlibAnalytic.LinearPMapClosedApproximateEigenpairStrongLimit
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace LinearPMap

/-- Finite exact eigenpairs embedded scale-by-scale into the domain of one target
partially defined operator. A common finite spectral index tracks the selected
finite eigenpairs across scales. The target residual is derived from the finite
eigenvalue equation and convergence to zero of the operator-embedding defect. -/
structure EmbeddedFiniteDistinctEigenpairStrongLimitData
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →ₗ.[ℝ] E)
    (witnessCount : ℕ) where
  FiniteState : ℕ → Type*
  [finiteNormedAddCommGroup : ∀ n, NormedAddCommGroup (FiniteState n)]
  [finiteInnerProductSpace : ∀ n, InnerProductSpace ℝ (FiniteState n)]
  finiteOperator : (n : ℕ) → FiniteState n →ₗ[ℝ] FiniteState n
  finiteEigenpair :
    (n : ℕ) → FiniteDistinctEigenpairData (finiteOperator n) witnessCount
  SpectralIndex : Type*
  [spectralFintype : Fintype SpectralIndex]
  finiteIndexEquiv : ∀ n, SpectralIndex ≃ (finiteEigenpair n).SpectralIndex
  embed : (n : ℕ) → FiniteState n →L[ℝ] E
  approximateVector : ℕ → SpectralIndex → A.domain
  approximateVector_coe :
    ∀ n k,
      (approximateVector n k : E) =
        embed n ((finiteEigenpair n).spectralVector (finiteIndexEquiv n k))
  spectralValue : SpectralIndex → ℝ
  spectralValue_injective : Function.Injective spectralValue
  spectralVector : SpectralIndex → E
  spectralVector_ne_zero : ∀ k, spectralVector k ≠ 0
  approximateValue_tendsto :
    ∀ k,
      Tendsto
        (fun n => (finiteEigenpair n).spectralValue (finiteIndexEquiv n k))
        atTop (nhds (spectralValue k))
  approximateVector_tendsto :
    ∀ k,
      Tendsto (fun n => (approximateVector n k : E)) atTop
        (nhds (spectralVector k))
  operatorCompatibility_tendsto_zero :
    ∀ k,
      Tendsto
        (fun n =>
          A (approximateVector n k) -
            embed n
              (finiteOperator n
                ((finiteEigenpair n).spectralVector
                  (finiteIndexEquiv n k))))
        atTop (nhds 0)

attribute [instance]
  EmbeddedFiniteDistinctEigenpairStrongLimitData.finiteNormedAddCommGroup
  EmbeddedFiniteDistinctEigenpairStrongLimitData.finiteInnerProductSpace
  EmbeddedFiniteDistinctEigenpairStrongLimitData.spectralFintype

namespace EmbeddedFiniteDistinctEigenpairStrongLimitData

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {A : E →ₗ.[ℝ] E}
variable {witnessCount : ℕ}

/-- The finite spectral value tracked by the common spectral index. -/
def approximateValue
    (D : EmbeddedFiniteDistinctEigenpairStrongLimitData A witnessCount)
    (n : ℕ) (k : D.SpectralIndex) : ℝ :=
  (D.finiteEigenpair n).spectralValue (D.finiteIndexEquiv n k)

/-- The finite exact eigenvector tracked by the common spectral index. -/
def finiteVector
    (D : EmbeddedFiniteDistinctEigenpairStrongLimitData A witnessCount)
    (n : ℕ) (k : D.SpectralIndex) : D.FiniteState n :=
  (D.finiteEigenpair n).spectralVector (D.finiteIndexEquiv n k)

@[simp] theorem finiteOperator_apply_finiteVector
    (D : EmbeddedFiniteDistinctEigenpairStrongLimitData A witnessCount)
    (n : ℕ) (k : D.SpectralIndex) :
    D.finiteOperator n (D.finiteVector n k) =
      D.approximateValue n k • D.finiteVector n k := by
  exact (D.finiteEigenpair n).apply_spectralVector (D.finiteIndexEquiv n k)

@[simp] theorem coe_approximateVector
    (D : EmbeddedFiniteDistinctEigenpairStrongLimitData A witnessCount)
    (n : ℕ) (k : D.SpectralIndex) :
    (D.approximateVector n k : E) = D.embed n (D.finiteVector n k) := by
  exact D.approximateVector_coe n k

/-- Tracking by equivalences preserves the requested finite witness count. -/
theorem spectralCard
    (D : EmbeddedFiniteDistinctEigenpairStrongLimitData A witnessCount) :
    Fintype.card D.SpectralIndex = witnessCount := by
  calc
    Fintype.card D.SpectralIndex =
        Fintype.card (D.finiteEigenpair 0).SpectralIndex :=
      Fintype.card_congr (D.finiteIndexEquiv 0)
    _ = witnessCount := (D.finiteEigenpair 0).spectralCard

/-- Finite exact eigen-equations turn the operator-embedding defect into the
target approximate-eigenpair residual. -/
theorem residual_tendsto_zero
    (D : EmbeddedFiniteDistinctEigenpairStrongLimitData A witnessCount)
    (k : D.SpectralIndex) :
    Tendsto
      (fun n =>
        A (D.approximateVector n k) -
          D.approximateValue n k • (D.approximateVector n k : E))
      atTop (nhds 0) := by
  simpa only [D.finiteOperator_apply_finiteVector, map_smul,
    D.coe_approximateVector] using
    D.operatorCompatibility_tendsto_zero k

noncomputable def toClosedLinearPMapFiniteApproximateEigenpairStrongLimitData
    (D : EmbeddedFiniteDistinctEigenpairStrongLimitData A witnessCount) :
    ClosedLinearPMapFiniteApproximateEigenpairStrongLimitData A witnessCount :=
  { SpectralIndex := D.SpectralIndex
    spectralFintype := D.spectralFintype
    approximateValue := D.approximateValue
    spectralValue := D.spectralValue
    spectralValue_injective := D.spectralValue_injective
    spectralCard := D.spectralCard
    approximateVector := D.approximateVector
    spectralVector := D.spectralVector
    spectralVector_ne_zero := D.spectralVector_ne_zero
    approximateValue_tendsto := D.approximateValue_tendsto
    approximateVector_tendsto := D.approximateVector_tendsto
    residual_tendsto_zero := D.residual_tendsto_zero }

end EmbeddedFiniteDistinctEigenpairStrongLimitData

end

end MathlibAnalytic
end MGAP4D
