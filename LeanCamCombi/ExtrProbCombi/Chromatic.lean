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

/-
-- two proofs
instance inter_fintype {s : Finset (Sym2 α)}: Fintype ↑({e: Sym2 α | ¬e.IsDiag} ↓∩ ↑s) :=
@Subtype.fintype _ _ (by simp; intros a; apply Finset.decidableMem) (Subtype.fintype _)
-- Fintype.ofFinset {e : ↑{e: Sym2 α | ¬e.IsDiag} | (e : Sym2 α) ∈ s} (by simp)
-/

def f := fun (x:  ↑{e: Sym2 α | ¬e.IsDiag}) => (x : Sym2 α)

-- def foo : Finset (Sym2 α) -> Set (Sym2 α) := fun x => x

-- opaque independent_set : Finset α

-- #check independent_set.sym2
-- #check (↑independent_set.sym2 : Set (Sym2 α))

-- def x : ↑({e: Sym2 α | ¬e.IsDiag} ↓∩ ↑s) :=
-- #check Finset.image f (({e : Sym2 α | ¬e.IsDiag} ↓∩ (↑ (independent_set.sym2))).toFinset)

-- A graph with an independent set
-- wrong
theorem independent_set_prob (independent_set : Finset α) : μ {ω | ∀ (x: ↑{e : Sym2 α | ¬ e.IsDiag}), x ∈ {e : ↑{e : Sym2 α | ¬ e.IsDiag} | (e : Sym2 α) ∈ independent_set.sym2}.toFinset → x ∉ ({e : Sym2 α | ¬ e.IsDiag} ↓∩ (G ω).edgeSet) } = (1-p)^(Nat.choose #independent_set 2) := by
rw [hG.meas_ne_subset]
apply congr <;> try rfl
simp [Finset.subtype]
rw [← @Finset.card_image_of_injective _ _ subtypeCoe.coe]
-- have : ∀ e, f e = ↑ e := by sorry

. -- rw [← Finset.filter_image]
  all_goals sorry
. apply Subtype.coe_injective



-- rw [Finset.card_sym2]


end ErdosRenyi
