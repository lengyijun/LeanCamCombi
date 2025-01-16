import LeanCamCombi.ExtrProbCombi.BernoulliSeq
import LeanCamCombi.ExtrProbCombi.BinomialRandomGraph
import LeanCamCombi.Mathlib.Data.Finset.Image

-- set_option pp.all true

/-!
Verify the second example in https://en.wikipedia.org/wiki/Probabilistic_method
-/

open scoped Finset ENNReal NNReal Set.Notation
open MeasureTheory ProbabilityTheory IsBernoulliSeq
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

def f := @Subtype.val (Sym2 α) (fun x => ¬ x.IsDiag)
-- def f := fun (x:  ↑{e: Sym2 α | ¬e.IsDiag}) => (x : Sym2 α)

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


-- rw [Finset.card_subtype]

let p := fun (e: Sym2 α) => ∀ a ∈ e, a ∈ independent_set

have h : (fun (e: {e: Sym2 α // ¬e.IsDiag}) ↦ ∀ a ∈ @Subtype.val (Sym2 α) (fun x => ¬ x.IsDiag) e, a ∈ independent_set) = (fun e => p (f e)):= by
  ext
  unfold p f
  simp

/-
have g : DecidablePred fun e: {e: Sym2 α // ¬e.IsDiag} => p (Subtype.val e) := by
  unfold p
  unfold DecidablePred
  intros b
  obtain ⟨b, d⟩ := b
  simp
  -- have : ∃ x y, s(x, y) = b := by simp
  -- rw [Sym2.mem_iff_mem]
  -- unfold Sym2.Mem
  all_goals sorry
-/

rw [← @Finset.card_image_of_injective _ _ f]

have decidable_p : DecidablePred p := by
  intros b
  apply Fintype.decidableForallFintype
have := @Finset.filter_image _ _ _ f Finset.univ p decidable_p
simp at this
unfold p f at this
unfold f
simp_all
rw [← this]
rw [univ_image_val]
-- . let s : Finset (Sym2 α) := {e | ∀ a ∈ e, a ∈ independent_set}
. rw [Finset.filter_comm]
  -- rw [Sym2.card_subtype_not_diag]
  let s : Finset (Sym2 α) := independent_set.sym2
  let t : Finset (Sym2 α) := {e | e.IsDiag}
  have g : #(s ∩ t) = #independent_set := by
    unfold s t
    rw [Finset.inter_comm, Finset.filter_inter]
    simp
    sorry
  have h := Finset.card_inter_add_card_sdiff s t
  rw [Finset.card_sym2] at h
  rw [g] at h
  have g : s \ t = (Finset.filter (fun x ↦ ¬x.IsDiag) (Finset.filter (fun e ↦ ∀ a ∈ e, a ∈ independent_set) Finset.univ)) := by
    unfold s t
    apply Finset.Subset.antisymm <;> intro x <;> simp
  rw [← g]
  have g : #(s \ t) = (#independent_set + 1).choose 2 - #independent_set := by omega
  unfold Nat.choose at g
  simp at g
  rw [g]
. apply Subtype.coe_injective


end ErdosRenyi
