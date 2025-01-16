import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

/-
theorem univ_image_val {α: Type*} [DecidableEq α] [Fintype α] (p : α → Prop) [DecidablePred p]: Finset.image Subtype.val (Finset.univ : Finset (Subtype p)) = {x : α | p x} := by apply Set.eq_of_subset_of_subset <;> simp
-/

theorem univ_image_val {α: Type*} [DecidableEq α] [Fintype α] (p : α → Prop) [DecidablePred p]: Finset.image Subtype.val (Finset.univ : Finset (Subtype p)) = ({x : α | p x} : Finset α) := by apply Finset.Subset.antisymm <;> intros x <;> simp
