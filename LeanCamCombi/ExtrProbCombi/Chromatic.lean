import LeanCamCombi.ExtrProbCombi.BernoulliSeq
import LeanCamCombi.ExtrProbCombi.BinomialRandomGraph

/-!
Verify the second example in https://en.wikipedia.org/wiki/Probabilistic_method
-/

open MeasureTheory ProbabilityTheory IsBernoulliSeq
open scoped Finset ENNReal NNReal Set.Notation

variable {α Ω : Type*} [DecidableEq α] [MeasurableSpace Ω] {G : Ω → SimpleGraph α} {H : SimpleGraph α} {p : ℝ≥0} (μ : Measure Ω) (hG : IsBinomialRandomGraph G p μ)
[IsProbabilityMeasure μ] [Fintype α]
[DecidableRel H.Adj]

namespace ErdosRenyi

include hG

-- def hh : Fintype {e : Sym2 α | ¬ e.IsDiag} := by sorry

-- A graph with an independent set
-- wrong
theorem independent_set_prob (independent_set : Finset α) : μ {ω | ∀ x ∈ ({e : Sym2 α | ¬ e.IsDiag} ↓∩ independent_set.sym2), x ∉ ({e : Sym2 α | ¬ e.IsDiag} ↓∩ (G ω).edgeSet) } = (1-p)^(Nat.choose #independent_set 2) := by

rw [hG.meas_ne_subset]

-- , Finset.card_sym2]

all_goals sorry

-- correct
-- theorem independent_set_prob (independent_set : Finset α) : μ {ω | ∀ x ∈ independent_set.sym2, x ∉ (G ω).edgeSet } = (1-p)^(Nat.choose #independent_set 2) := by

end ErdosRenyi
