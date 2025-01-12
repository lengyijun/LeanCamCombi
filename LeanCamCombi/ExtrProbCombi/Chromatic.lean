import LeanCamCombi.ExtrProbCombi.BernoulliSeq
import LeanCamCombi.ExtrProbCombi.Basic

/-!
Verify the second example in https://en.wikipedia.org/wiki/Probabilistic_method
-/

open MeasureTheory ProbabilityTheory IsBernoulliSeq
open scoped Finset ENNReal NNReal

variable {α Ω : Type*} [MeasurableSpace Ω] {G : Ω → SimpleGraph α} {H : SimpleGraph α} {p : ℝ≥0} (μ : Measure Ω) (hG : ErdosRenyi G p μ)
[IsProbabilityMeasure μ] [Fintype α]
[DecidableRel H.Adj]

namespace ErdosRenyi

include hG

-- A graph with an independent set
theorem independent_set_prob (independent_set : Finset α) : μ {ω | ∀ x ∈ independent_set.sym2, x ∉ (G ω).edgeSet } = (1-p)^(Nat.choose (#independent_set + 1) 2) := by
rw [hG.meas_ne_subset, Finset.card_sym2]

end ErdosRenyi
