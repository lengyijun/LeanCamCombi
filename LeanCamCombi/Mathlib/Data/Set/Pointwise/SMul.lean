import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Action.Opposite
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Set.Pointwise.SMul

open MulOpposite
open scoped Pointwise

namespace Set
variable {α β : Type*}

section Mul
variable [Mul α] {s t : Set α} {a : α}

@[to_additive (attr := simp)]
lemma singleton_mul' (a : α) (s : Set α) : {a} * s = a • s := singleton_mul

@[to_additive (attr := simp)]
lemma mul_singleton' (s : Set α) (a : α) : s * {a} = op a • s := mul_singleton

@[to_additive]
lemma smul_set_subset_mul : a ∈ s → a • t ⊆ s * t := image_subset_image2_right

@[to_additive] lemma pair_mul (a b : α) (s : Set α) : {a, b} * s = a • s ∪ b • s := by
  rw [insert_eq, union_mul, singleton_mul', singleton_mul']

open scoped RightActions
@[to_additive] lemma mul_pair (s : Set α) (a b : α) : s * {a, b} = s <• a ∪ s <• b := by
  rw [insert_eq, mul_union, mul_singleton', mul_singleton']

end Mul

section Group
variable [Group α] {s t : Set α} {a b : α}

@[to_additive (attr := simp)]
lemma mem_smul_set_inv : a ∈ b • s⁻¹ ↔ b ∈ a • s := by simp [mem_smul_set_iff_inv_smul_mem]

@[to_additive exists_inter_subset_two_nsmul_inter_two_nsmul]
lemma exists_smul_inter_smul_subset_smul_sq_inter_sq (hs : s⁻¹ = s) (ht : t⁻¹ = t) (a b : α) :
    ∃ z : α, a • s ∩ b • t ⊆ z • (s ^ 2 ∩ t ^ 2) := by
  obtain hAB | ⟨z, hzA, hzB⟩ := (a • s ∩ b • t).eq_empty_or_nonempty
  · exact ⟨1, by simp [hAB]⟩
  refine ⟨z, ?_⟩
  calc
    a • s ∩ b • t ⊆ (z • s⁻¹) * s ∩ ((z • t⁻¹) * t) := by
      gcongr <;> apply smul_set_subset_mul <;> simpa
    _ = z • (s ^ 2 ∩ t ^ 2) := by simp_rw [Set.smul_set_inter, sq, smul_mul_assoc, hs, ht]

end Group
end Set

namespace Set
variable {α β : Type*}

section Monoid
variable [Monoid α] [MulAction α β] {s : Set β} {a : α} {b : β}

@[simp] lemma mem_invOf_smul_set [Invertible a] : b ∈ ⅟a • s ↔ a • b ∈ s :=
  mem_inv_smul_set_iff (a := unitOfInvertible a)

end Monoid

section Group
variable [Group α] [MulAction α β] {s : Set β} {t : Set β} {a : α}

@[to_additive (attr := simp)]
lemma smul_set_subset_smul_set_iff : a • s ⊆ a • t ↔ s ⊆ t :=
  image_subset_image_iff <| MulAction.injective _

end Group
end Set
