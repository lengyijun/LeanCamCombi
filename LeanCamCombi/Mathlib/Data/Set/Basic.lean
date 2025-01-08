import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Subsingleton

namespace Set
variable {α : Type*} {s : Set α} {a : α}

lemma sdiff_inter_right_comm (s t u : Set α) : s \ t ∩ u = (s ∩ u) \ t := by
  ext; simp [and_right_comm]

lemma inter_sdiff_left_comm (s t u : Set α) : s ∩ (t \ u) = t ∩ (s \ u) := by
  simp_rw [← inter_diff_assoc, inter_comm]

theorem subset_bool_iff_eq (s : Set Prop) : s ⊆ {True, False} ↔ s = ∅ \/ s = {True} \/ s = {False} \/ s = {True, False} := by
constructor <;> intros h
. by_cases True ∈ s <;> by_cases False ∈ s
  . have : {True, False} ⊆ s := by  intros x hx
                                    have g : x = True \/ x = False := by simp_all
                                    cases g <;> subst x <;> simp_all
    right; right; right
    apply Set.eq_of_subset_of_subset <;> assumption
  . right; left
    apply Set.eq_of_subset_of_subset <;> intros x hx
    . by_cases x <;> simp_all
    . simp_all
  . right; right; left
    apply Set.eq_of_subset_of_subset <;> intros x hx
    . by_cases x <;> simp_all
    . simp_all
  . left
    apply Set.eq_of_subset_of_subset <;> intros x hx
    . by_cases x <;> simp_all
    . simp_all
. match h with
  | Or.inl h => subst s; simp
  | Or.inr (Or.inl h) => subst s; simp
  | Or.inr (Or.inr (Or.inl h)) => subst s; simp
  | Or.inr (Or.inr (Or.inr h)) => subst s; simp

theorem subset_bool_iff_eq' (s : Set Prop) : s = ∅ \/ s = {True} \/ s = {False} \/ s = {True, False} := by
rw [← subset_bool_iff_eq, ← Set.univ_eq_true_false]
apply Set.subset_univ

end Set
