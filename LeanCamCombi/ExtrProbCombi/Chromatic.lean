import LeanCamCombi.ExtrProbCombi.BernoulliSeq
import LeanCamCombi.ExtrProbCombi.BinomialRandomGraph

/-!
Verify the second example in https://en.wikipedia.org/wiki/Probabilistic_method
-/

open MeasureTheory ProbabilityTheory IsBernoulliSeq
open scoped Finset ENNReal NNReal Set.Notation

variable {α Ω : Type*} [DecidableEq α] [Fintype α] [MeasurableSpace Ω] {G : Ω → SimpleGraph α} (μ : Measure Ω) [IsProbabilityMeasure μ] {p : ℝ≥0} (hG : IsBinomialRandomGraph G p μ)
-- {H : SimpleGraph α} [DecidableRel H.Adj]

namespace ErdosRenyi

include hG

instance inter_fintype {s : Finset (Sym2 α)}: Fintype ↑({e: Sym2 α | ¬e.IsDiag} ↓∩ ↑s) :=
Fintype.ofFinset {e : ↑{e: Sym2 α | ¬e.IsDiag} | (e : Sym2 α) ∈ s} (by simp)

-- A graph with an independent set
-- wrong
theorem independent_set_prob (independent_set : Finset α) : μ {ω | ∀ x ∈ ({e : Sym2 α | ¬ e.IsDiag} ↓∩ independent_set.sym2).toFinset, x ∉ ({e : Sym2 α | ¬ e.IsDiag} ↓∩ (G ω).edgeSet) } = (1-p)^(Nat.choose #independent_set 2) := by

rw [hG.meas_ne_subset]
apply congr <;> try rfl

simp

-- rw [Finset.card_sym2]

all_goals sorry

-- correct
-- theorem independent_set_prob (independent_set : Finset α) : μ {ω | ∀ x ∈ independent_set.sym2, x ∉ (G ω).edgeSet } = (1-p)^(Nat.choose #independent_set 2) := by

end ErdosRenyi
