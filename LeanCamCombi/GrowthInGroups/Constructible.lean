/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Tactic.StacksAttribute
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Spectral.Hom
import LeanCamCombi.Mathlib.Data.Set.Image
import LeanCamCombi.Mathlib.Topology.Defs.Induced
import LeanCamCombi.GrowthInGroups.BooleanSubalgebra

/-!
# Constructible sets
-/

open Set TopologicalSpace

variable {ι : Sort*} {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {f : α → β}
  {s t U : Set α} {a : α}

/-! ### Retrocompact sets -/

@[stacks 005A]
def IsRetroCompact (s : Set α) : Prop := ∀ ⦃U⦄, IsCompact U → IsOpen U → IsCompact (s ∩ U)

@[simp] lemma IsRetroCompact.empty : IsRetroCompact (∅ : Set α) := by simp [IsRetroCompact]

@[simp] lemma IsRetroCompact.singleton : IsRetroCompact {a} :=
  fun _ _ _ ↦ Subsingleton.singleton_inter.isCompact

lemma IsRetroCompact.union (hs : IsRetroCompact s) (ht : IsRetroCompact t) :
    IsRetroCompact (s ∪ t : Set α) :=
  fun _U hUcomp hUopen ↦ union_inter_distrib_right .. ▸ (hs hUcomp hUopen).union (ht hUcomp hUopen)

lemma IsRetroCompact.inter [T2Space α] (hs : IsRetroCompact s) (ht : IsRetroCompact t) :
    IsRetroCompact (s ∩ t : Set α) :=
  fun _U hUcomp hUopen ↦ inter_inter_distrib_right .. ▸ (hs hUcomp hUopen).inter (ht hUcomp hUopen)

lemma IsRetroCompact.inter_isOpen (hs : IsRetroCompact s) (ht : IsRetroCompact t)
    (htopen : IsOpen t) : IsRetroCompact (s ∩ t : Set α) :=
  fun _U hUcomp hUopen ↦ inter_assoc .. ▸ hs (ht hUcomp hUopen) (htopen.inter hUopen)

lemma IsRetroCompact.isOpen_inter (hs : IsRetroCompact s) (ht : IsRetroCompact t)
    (hsopen : IsOpen s) : IsRetroCompact (s ∩ t : Set α) :=
  inter_comm .. ▸ ht.inter_isOpen hs hsopen

lemma isRetroCompact_iff_isSpectralMap_subtypeVal :
    IsRetroCompact s ↔ IsSpectralMap (Subtype.val : s → α) := by
  refine ⟨fun hs ↦ ⟨continuous_subtype_val, fun t htopen htcomp ↦ ?_⟩, fun hs t htcomp htopen ↦ ?_⟩
  · rw [IsEmbedding.subtypeVal.isCompact_iff, image_preimage_eq_inter_range,
      Subtype.range_coe_subtype, setOf_mem_eq, inter_comm]
    exact hs htcomp htopen
  · simpa using (hs.isCompact_preimage_of_isOpen htopen htcomp).image continuous_subtype_val

@[stacks 005B]
lemma IsRetroCompact.image_of_isEmbedding (hs : IsRetroCompact s) (hfemb : IsEmbedding f)
    (hfcomp : IsRetroCompact (range f)) : IsRetroCompact (f '' s) := by
  rintro U hUcomp hUopen
  rw [← image_inter_preimage, ← hfemb.isCompact_iff]
  refine hs ?_ <| hUopen.preimage hfemb.continuous
  rw [hfemb.isCompact_iff, image_preimage_eq_inter_range, inter_comm]
  exact hfcomp hUcomp hUopen

@[stacks 005J] -- Extracted from the proof of `005J`
lemma IsRetroCompact.preimage_of_isOpenEmbedding {s : Set β} (hf : IsOpenEmbedding f)
    (hs : IsRetroCompact s) : IsRetroCompact (f ⁻¹' s) := by
  rintro U hUcomp hUopen
  rw [hf.isCompact_iff, image_preimage_inter]
  exact hs (hUcomp.image hf.continuous) <| hf.isOpenMap _ hUopen

@[stacks 09YE] -- Extracted from the proof of `09YE`
lemma IsRetroCompact.preimage_of_isClosedEmbedding {s : Set β} (hf : IsClosedEmbedding f)
    (hf' : IsCompact (Set.range f)ᶜ) (hs : IsRetroCompact s)  : IsRetroCompact (f ⁻¹' s) := by
  rintro U hUcomp hUopen
  have hfUopen : IsOpen (f '' U ∪ (range f)ᶜ) := by
    simpa [image_compl_eq_range_sdiff_image hf.injective, sdiff_eq, compl_inter, union_comm]
      using (hf.isClosedMap _ hUopen.isClosed_compl).isOpen_compl
  have hfUcomp : IsCompact (f '' U ∪ (range f)ᶜ) := (hUcomp.image hf.continuous).union hf'
  simpa [inter_union_distrib_left, inter_left_comm, inter_eq_right.2 (image_subset_range ..),
    hf.isCompact_iff, image_preimage_inter] using (hs hfUcomp hfUopen).inter_left hf.isClosed_range

/-! ### Constructible sets -/

/-- A constructible set is a set that can be written as the
finite union/finite intersection/complement of open retrocompact sets.

In other words, constructible sets form the boolean subalgebra generated by open retrocompact sets.
-/
def IsConstructible (s : Set α) : Prop :=
  s ∈ BooleanSubalgebra.closure {U | IsOpen U ∧ IsRetroCompact U}

@[simp]
protected lemma IsConstructible.empty : IsConstructible (∅ : Set α) := BooleanSubalgebra.bot_mem

@[simp]
protected lemma IsConstructible.univ : IsConstructible (univ : Set α) := BooleanSubalgebra.top_mem

lemma IsConstructible.union : IsConstructible s → IsConstructible t → IsConstructible (s ∪ t) :=
  BooleanSubalgebra.sup_mem

lemma IsConstructible.inter : IsConstructible s → IsConstructible t → IsConstructible (s ∩ t) :=
  BooleanSubalgebra.inf_mem

lemma IsConstructible.sdiff : IsConstructible s → IsConstructible t → IsConstructible (s \ t) :=
  BooleanSubalgebra.sdiff_mem

lemma IsConstructible.himp : IsConstructible s → IsConstructible t → IsConstructible (s ⇨ t) :=
  BooleanSubalgebra.himp_mem

@[simp] lemma isConstructible_compl : IsConstructible sᶜ ↔ IsConstructible s :=
  BooleanSubalgebra.compl_mem_iff

alias ⟨IsConstructible.of_compl, IsConstructible.compl⟩ := isConstructible_compl

lemma IsConstructible.iUnion [Finite ι] {f : ι → Set α} (hf : ∀ i, IsConstructible (f i)) :
    IsConstructible (⋃ i, f i) := BooleanSubalgebra.iSup_mem hf

lemma IsConstructible.iInter [Finite ι] {f : ι → Set α} (hf : ∀ i, IsConstructible (f i)) :
    IsConstructible (⋂ i, f i) := BooleanSubalgebra.iInf_mem hf

lemma IsConstructible.sUnion {S : Set (Set α)} (hS : S.Finite) (hS' : ∀ s ∈ S, IsConstructible s) :
    IsConstructible (⋃₀ S) := BooleanSubalgebra.sSup_mem hS hS'

lemma IsConstructible.sInter {S : Set (Set α)} (hS : S.Finite) (hS' : ∀ s ∈ S, IsConstructible s) :
    IsConstructible (⋂₀ S) := BooleanSubalgebra.sInf_mem hS hS'

lemma IsConstructible.biUnion {ι : Type*} {f : ι → Set α} {t : Set ι} (ht : t.Finite)
    (hf : ∀ i ∈ t, IsConstructible (f i)) : IsConstructible (⋃ i ∈ t, f i) :=
  BooleanSubalgebra.biSup_mem ht hf

lemma IsConstructible.biInter {ι : Type*} {f : ι → Set α} {t : Set ι} (ht : t.Finite)
    (hf : ∀ i ∈ t, IsConstructible (f i)) : IsConstructible (⋂ i ∈ t, f i) :=
  BooleanSubalgebra.biInf_mem ht hf

lemma IsRetroCompact.isConstructible (hUopen : IsOpen U) (hUcomp : IsRetroCompact U) :
    IsConstructible U := BooleanSubalgebra.subset_closure ⟨hUopen, hUcomp⟩

/-- An induction principle for constructible sets. If `p` holds for all open retrocompact
sets, and is preserved under union and complement, then `p` holds for all constructible sets. -/
@[elab_as_elim]
lemma IsConstructible.empty_union_induction {p : ∀ s : Set α, IsConstructible s → Prop}
    (open_retrocompact : ∀ U (hUopen : IsOpen U) (hUcomp : IsRetroCompact U),
      p U (BooleanSubalgebra.subset_closure ⟨hUopen, hUcomp⟩))
    (union : ∀ s hs t ht, p s hs → p t ht → p (s ∪ t) (hs.union ht))
    (compl : ∀ s hs, p s hs → p sᶜ hs.compl) {s} (hs : IsConstructible s) : p s hs := by
  induction hs using BooleanSubalgebra.closure_bot_sup_induction with
  | mem U hU => exact open_retrocompact _ hU.1 hU.2
  | bot => exact open_retrocompact _ isOpen_empty .empty
  | sup s hs t ht hs' ht' => exact union _ _ _ _ hs' ht'
  | compl s hs hs' => exact compl _ _ hs'

/-- If `f` is continuous and is such that preimages of retrocompact sets are retrocompact, then
preimages of constructible sets are constructible. -/
@[stacks 005I]
lemma IsConstructible.preimage {s : Set β} (hfcont : Continuous f)
    (hf : ∀ s, IsRetroCompact s → IsRetroCompact (f ⁻¹' s)) (hs : IsConstructible s) :
    IsConstructible (f ⁻¹' s) := by
  induction hs using IsConstructible.empty_union_induction with
  | open_retrocompact U hUopen hUcomp =>
    exact (hf _ hUcomp).isConstructible <| hUopen.preimage hfcont
  | union s hs t ht hs' ht' => rw [preimage_union]; exact hs'.union ht'
  | compl s hs hs' => rw [preimage_compl]; exact hs'.compl

@[stacks 005J]
lemma IsConstructible.preimage_of_isOpenEmbedding {s : Set β} (hf : IsOpenEmbedding f)
    (hs : IsConstructible s) : IsConstructible (f ⁻¹' s) :=
  hs.preimage hf.continuous fun _t ht ↦ ht.preimage_of_isOpenEmbedding hf

@[stacks 09YE]
lemma IsConstructible.preimage_of_isClosedEmbedding {s : Set β} (hf : IsClosedEmbedding f)
    (hf' : IsCompact (Set.range f)ᶜ) (hs : IsConstructible s) : IsConstructible (f ⁻¹' s) :=
  hs.preimage hf.continuous fun _t ht ↦ ht.preimage_of_isClosedEmbedding hf hf'

@[stacks 09YD]
lemma IsConstructible.image_of_isOpenEmbedding (hfopen : IsOpenEmbedding f)
    (hfcomp : IsRetroCompact (Set.range f)) (hs : IsConstructible s) : IsConstructible (f '' s) := by
  induction hs using IsConstructible.empty_union_induction with
  | open_retrocompact U hUopen hUcomp =>
    exact (hUcomp.image_of_isEmbedding hfopen.isEmbedding hfcomp).isConstructible <|
      hfopen.isOpenMap _ hUopen
  | union s hs t ht hs' ht' => rw [image_union]; exact hs'.union ht'
  | compl s hs hs' =>
    rw [image_compl_eq_range_sdiff_image hfopen.injective]
    exact (hfcomp.isConstructible hfopen.isOpen_range).sdiff hs'

@[stacks 09YG]
lemma IsConstructible.image_of_isClosedEmbedding (hf : IsClosedEmbedding f)
    (hfcomp : IsRetroCompact (Set.range f)ᶜ) (hs : IsConstructible s) : IsConstructible (f '' s) := by
  induction hs using IsConstructible.empty_union_induction with
  | open_retrocompact U hUopen hUcomp =>
    have hfU : IsOpen (f '' U ∪ (range f)ᶜ) := by
      simpa [image_compl_eq_range_sdiff_image hf.injective, sdiff_eq, compl_inter, union_comm]
        using (hf.isClosedMap _ hUopen.isClosed_compl).isOpen_compl
    suffices h : IsRetroCompact (f '' U ∪ (range f)ᶜ) by
      simpa [union_inter_distrib_right, inter_eq_left.2 (image_subset_range ..)]
        using (h.isConstructible hfU).sdiff (hfcomp.isConstructible hf.isClosed_range.isOpen_compl)
    rintro V hVcomp hVopen
    rw [union_inter_distrib_right, ← image_inter_preimage]
    exact ((hUcomp (hf.isCompact_preimage hVcomp) (hVopen.preimage hf.continuous)).image
      hf.continuous).union <| hfcomp hVcomp hVopen
  | union s hs t ht hs' ht' => rw [image_union]; exact hs'.union ht'
  | compl s hs hs' =>
    rw [image_compl_eq_range_sdiff_image hf.injective]
    exact (hfcomp.isConstructible hf.isClosed_range.isOpen_compl).of_compl.sdiff hs'

section CompactSpace
variable [CompactSpace α] {P : ∀ s : Set α, IsConstructible s → Prop} {b : ι → Set α}

lemma IsRetroCompact.isCompact (hs : IsRetroCompact s) : IsCompact s := by
  simpa using hs CompactSpace.isCompact_univ

lemma TopologicalSpace.IsTopologicalBasis.isRetroCompact_iff_isCompact
    (basis : IsTopologicalBasis (range b)) (compact_inter : ∀ i j, IsCompact (b i ∩ b j))
    (hU : IsOpen U) : IsRetroCompact U ↔ IsCompact U := by
  refine ⟨IsRetroCompact.isCompact, fun hU' {V} hV' hV ↦ ?_⟩
  have hb (i : PLift ι) : IsCompact (b i.down) := by simpa using compact_inter i.down i.down
  have := isCompact_open_iff_eq_finite_iUnion_of_isTopologicalBasis (b ∘ PLift.down)
    (by simpa [PLift.down_surjective.range_comp] using basis) hb
  obtain ⟨s, hs, rfl⟩ := (this U).mp ⟨hU', hU⟩
  obtain ⟨t, ht, rfl⟩ := (this V).mp ⟨hV', hV⟩
  simp only [Set.iUnion_inter, Set.inter_iUnion]
  exact ht.isCompact_biUnion fun _ _ ↦ hs.isCompact_biUnion fun _ _ ↦ compact_inter ..

lemma TopologicalSpace.IsTopologicalBasis.isRetroCompact (basis : IsTopologicalBasis (range b))
    (compact_inter : ∀ i j, IsCompact (b i ∩ b j)) (i : ι) : IsRetroCompact (b i) :=
  (basis.isRetroCompact_iff_isCompact compact_inter <| basis.isOpen <| mem_range_self _).2 <| by
    simpa using compact_inter i i

lemma TopologicalSpace.IsTopologicalBasis.isConstructible (basis : IsTopologicalBasis (range b))
    (compact_inter : ∀ i j, IsCompact (b i ∩ b j)) (i : ι) : IsConstructible (b i) :=
  (basis.isRetroCompact compact_inter _).isConstructible <| basis.isOpen <| mem_range_self _

@[elab_as_elim]
lemma IsConstructible.induction_of_isTopologicalBasis {ι : Type*} (b : ι → Set α)
    (basis : IsTopologicalBasis (range b)) (compact_inter : ∀ i j, IsCompact (b i ∩ b j))
    (sdiff : ∀ i s (hs : Set.Finite s), P (b i \ ⋃ j ∈ s, b j)
      ((basis.isConstructible compact_inter _).sdiff <| .biUnion hs fun i _ ↦
        basis.isConstructible compact_inter _))
    (union : ∀ s hs t ht, P s hs → P t ht → P (s ∪ t) (hs.union ht))
    (s : Set α) (hs : IsConstructible s) : P s hs := by
  sorry

end CompactSpace

/-! ### Locally constructible sets -/

/-- A set in a topological space is locally constructible, if it can be partitioned along a finite
open cover such that every part is constructible -/
@[stacks 005G]
def IsLocallyConstructible (s : Set α) : Prop :=
  ∃ F : Set (Set α), (∀ x, ∃ U ∈ F, x ∈ U) ∧ (∀ U ∈ F, IsOpen U) ∧ ∀ U ∈ F, IsConstructible (s ∩ U)

lemma IsLocallyConstructible.of_iUnion {ι : Sort*} {f : ι → Set α} (cover : ∀ x, ∃ i, x ∈ f i)
    (isOpen : ∀ i, IsOpen (f i)) (constructible : ∀ i, IsConstructible (s ∩ f i)) :
    IsLocallyConstructible s := ⟨range f, by simpa, by simpa, by simpa⟩

lemma IsConstructible.isLocallyConstructible (hs : IsConstructible s) : IsLocallyConstructible s :=
  ⟨{univ}, by simpa⟩

lemma IsRetroCompact.isLocallyConstructible (hUopen : IsOpen U) (hUcomp : IsRetroCompact U) :
    IsLocallyConstructible U := (hUcomp.isConstructible hUopen).isLocallyConstructible

@[simp] protected lemma IsLocallyConstructible.empty : IsLocallyConstructible (∅ : Set α) :=
  IsConstructible.empty.isLocallyConstructible

@[simp] protected lemma IsLocallyConstructible.univ : IsLocallyConstructible (univ : Set α) :=
  IsConstructible.univ.isLocallyConstructible

lemma IsLocallyConstructible.inter :
    IsLocallyConstructible s → IsLocallyConstructible t → IsLocallyConstructible (s ∩ t) := by
  rintro ⟨F, hFcov, hFopen, hFcons⟩ ⟨G, hGcov, hGopen, hGcons⟩
  refine .of_iUnion (f := fun ((U, V) : F × G) ↦ U.1 ∩ V.1) (fun x ↦ ?_)
    (fun (⟨U, hU⟩, ⟨V, hV⟩) ↦ (hFopen _ hU).inter (hGopen _ hV)) fun (⟨U, hU⟩, ⟨V, hV⟩) ↦ ?_
  · obtain ⟨U, hU, hxU⟩ := hFcov x
    obtain ⟨V, hV, hxV⟩ := hGcov x
    exact ⟨(⟨U, hU⟩, ⟨V, hV⟩), hxU, hxV⟩
  · rw [inter_inter_inter_comm]
    exact (hFcons _ hU).inter (hGcons _ hV)

private lemma infClosed_isLocallyConstructible : InfClosed {s : Set α | IsLocallyConstructible s} :=
  fun _s hs _t ht ↦ hs.inter ht

lemma IsLocallyConstructible.iInter [Finite ι] {f : ι → Set α}
    (hf : ∀ i, IsLocallyConstructible (f i)) : IsLocallyConstructible (⋂ i, f i) :=
  infClosed_isLocallyConstructible.iInf_mem .univ hf

lemma IsLocallyConstructible.sInter {S : Set (Set α)} (hS : S.Finite)
    (hS' : ∀ s ∈ S, IsLocallyConstructible s) : IsLocallyConstructible (⋂₀ S) :=
  infClosed_isLocallyConstructible.sInf_mem hS .univ hS'
