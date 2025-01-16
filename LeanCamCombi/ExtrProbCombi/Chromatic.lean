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

def independent_set: SimpleGraph α → Finset α → Prop := fun g s => Disjoint (({e : ↑{e : Sym2 α | ¬ e.IsDiag} | (e : Sym2 α) ∈ s.sym2} : Finset _) : Set _) ({e : Sym2 α | ¬ e.IsDiag} ↓∩ g.edgeSet)

def f := @Subtype.val (Sym2 α) (fun x => ¬ x.IsDiag)

-- A graph with an independent set
theorem independent_set_prob (s: Finset α) : μ {ω | independent_set (G ω) s} = (1-p)^(Nat.choose #s 2) := by
unfold independent_set
rw [hG.meas_ne_subset]
apply congr <;> try rfl
simp [Finset.subtype]
rw [← @Finset.card_image_of_injective _ _ f]

. let p := fun (e: Sym2 α) => ∀ a ∈ e, a ∈ s
  have decidable_p : DecidablePred p := by
    intros b
    apply Fintype.decidableForallFintype
  have h := @Finset.filter_image _ _ _ f Finset.univ p decidable_p
  simp at h
  unfold p f at h
  have : (fun (e: {e: Sym2 α // ¬e.IsDiag}) ↦ ∀ a ∈ @Subtype.val (Sym2 α) (fun x => ¬ x.IsDiag) e, a ∈ s) = (fun e => p (f e)):= by
    ext
    unfold p f
    simp
  unfold f
  simp_all
  rw [← h]
  rw [univ_image_val]
  rw [← Sym2.card_image_offDiag]
  apply congr <;> try rfl
  apply Finset.Subset.antisymm
  . intros x hx
    simp_all
    obtain ⟨_, _⟩ := hx
    have h := @Sym2.exists α (fun y => y = x)
    simp at h
    obtain ⟨y, z, _⟩ := h
    subst x
    use y
    use z
    simp_all
  . intros x hx
    simp_all
    obtain ⟨c, d, ⟨⟨_, _, _⟩, _⟩⟩ := hx
    subst x
    simp_all
. apply Subtype.coe_injective

theorem cassava (y : ℕ): μ {ω | ∃ (s : Finset α), (s.card = y) /\ independent_set (G ω) s} ≤ (Nat.choose (Fintype.card α) y) * (1-p)^(Nat.choose y 2):= by
let ss : Finset (Finset α) := {vs | #vs = y}
let k : Set Ω := ⋃ i ∈ ss, {ω | independent_set (G ω) i}
apply LE.le.trans
. have h : {ω | ∃ (s : Finset α), (s.card = y) /\ independent_set (G ω) s} ⊆ k := by
    intros w hw
    obtain ⟨s, _, _⟩ := hw
    unfold k ss
    simp_all
    use s
  apply μ.mono at h
  exact h
. apply LE.le.trans
  . unfold k
    apply @MeasureTheory.measure_biUnion_finset_le _ _ _ _ _ μ ss (fun i => {ω | independent_set (G ω) i})
  . let f i := μ {ω | independent_set (G ω) i}
    let g (i : Finset α) := (1-p)^(Nat.choose y 2)
    have h : ∀ i ∈ ss, f i ≤ g i := by
      unfold f g
      intros s _
      unfold ss at *
      simp_all
      rw [independent_set_prob]
      any_goals assumption
      subst y
      norm_num
    apply Finset.sum_le_sum at h
    unfold g at h
    simp at h
    have g := @Fintype.card_finset_len α _ y
    rw [Fintype.card_subtype] at g
    rw [g] at h
    assumption

end ErdosRenyi
