/-
Copyright (c) 2022 Yaël Dillies, Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Kexing Ying
-/
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Basic
import LeanCamCombi.Mathlib.Probability.ProbabilityMassFunction.Constructions
import LeanCamCombi.Mathlib.Data.Set.Basic

/-!
# Sequences of iid Bernoulli random variables

This file defines sequences of independent `p`-Bernoulli random variables and proves that the
complement of a sequence of independent Bernoulli random variables, union/intersection of two
independent sequences of independent Bernoulli random variables, are themselves sequences of
independent Bernoulli random variables.

## Main declarations

* `ProbabilityTheory.IsBernoulliSeq`: Typeclass for a sequence of iid Bernoulli random variables
  with parameter `p`
-/

open Fintype MeasureTheory Set
open scoped Finset MeasureTheory ProbabilityTheory ENNReal NNReal

namespace ProbabilityTheory
variable {α Ω : Type*} [MeasurableSpace Ω]

/-- We say a `set α`-valued random is a sequence of iid Bernoulli random variables with parameter
`p` if `p ≤ 1`, the `a` projections (for `a : α`) are independent and are `p`-Bernoulli distributed.
-/
structure IsBernoulliSeq (X : Ω → Set α) (p : outParam ℝ≥0) (μ : Measure Ω := by volume_tac) : Prop
    where
  protected le_one : p ≤ 1
  protected iIndepFun : iIndepFun (fun _ => inferInstance) (fun a ω ↦ a ∈ X ω) μ
  protected map : ∀ a, Measure.map (fun ω ↦ a ∈ X ω) μ = (PMF.bernoulli' p le_one).toMeasure

variable {X Y : Ω → Set α} {μ : Measure Ω} {p q : ℝ≥0} (hX : IsBernoulliSeq X p μ)
  (hY : IsBernoulliSeq Y q μ)

namespace IsBernoulliSeq

include hX

protected lemma ne_zero [Nonempty α] : μ ≠ 0 :=
  Nonempty.elim ‹_› fun a h ↦ (PMF.bernoulli' p hX.le_one).toMeasure_ne_zero $ by
    rw [← hX.map a, h, Measure.map_zero]

protected lemma aemeasurable (a : α) : AEMeasurable (fun ω ↦ a ∈ X ω) μ := by
  classical
  have : (PMF.bernoulli' p hX.le_one).toMeasure ≠ 0 := NeZero.ne _
  rw [← hX.map a, Measure.map] at this
  refine (Ne.dite_ne_right_iff fun hX' ↦ ?_).1 this
  rw [Measure.mapₗ_ne_zero_iff hX'.measurable_mk]
  haveI : Nonempty α := ⟨a⟩
  exact hX.ne_zero

@[simp] protected lemma nullMeasurableSet (a : α) : NullMeasurableSet {ω | a ∈ X ω} μ := by
  rw [(by ext; simp : {ω | a ∈ X ω} = (fun ω ↦ a ∈ X ω) ⁻¹' {True})]
  exact (hX.aemeasurable a).nullMeasurableSet_preimage MeasurableSpace.measurableSet_top

protected lemma identDistrib (a j : α) : IdentDistrib (fun ω ↦ a ∈ X ω) (fun ω ↦ X ω j) μ μ :=
  { aemeasurable_fst := hX.aemeasurable _
    aemeasurable_snd := hX.aemeasurable _
    map_eq := (hX.map _).trans (hX.map _).symm }

@[simp] lemma meas_apply (a : α) : μ {ω | a ∈ X ω} = p := by
  rw [(_ : {ω | a ∈ X ω} = (fun ω ↦ a ∈ X ω) ⁻¹' {True}),
    ← Measure.map_apply_of_aemeasurable (hX.aemeasurable a) MeasurableSpace.measurableSet_top]
  · simp [hX.map]
  · simp

@[simp] lemma meas_apply' (a : α) : μ {ω | a ∉ X ω} = 1-p := by
  rw [(_ : {ω | a ∉ X ω} = (fun ω ↦ a ∈ X ω) ⁻¹' {False}),
    ← Measure.map_apply_of_aemeasurable (hX.aemeasurable a) MeasurableSpace.measurableSet_top]
  . simp [hX.map]
  . simp

/-
lemma IsProbabilityMeasure_μ (non_empty : ∃ a : α, True) : IsProbabilityMeasure μ := ⟨
by  have h : ∀ (a : α), μ {ω | a ∈ X ω} + μ {ω | a ∉ X ω} = 1:= by
      intros a
      rw [hX.meas_apply, hX.meas_apply']
      have h : p + (1 - p) = 1 := by
        rw [← (add_tsub_assoc_of_le hX.le_one) p]
        rw [← tsub_add_eq_add_tsub]
        all_goals norm_num
      assumption_mod_cast
    obtain ⟨a, _⟩ := non_empty
    specialize h a
    -- {ω | a ∈ X ω} maybe not measurable
    sorry
⟩
-/

protected lemma meas [IsProbabilityMeasure (μ : Measure Ω)] [Fintype α] (s : Finset α) :
    μ {ω | X ω = s} = p ^ #s * (1 - p) ^ (card α - #s) := by
  classical
  simp_rw [Set.ext_iff, setOf_forall]
  rw [hX.iIndepFun.meas_iInter, ← s.prod_mul_prod_compl, Finset.prod_eq_pow_card,
    Finset.prod_eq_pow_card, Finset.card_compl]
  · rintro a hi
    rw [Finset.mem_compl] at hi
    simp only [hi, ← compl_setOf, prob_compl_eq_one_sub₀, mem_setOf_eq, Finset.mem_coe,
      iff_false, hX.nullMeasurableSet, hX.meas_apply]
  · rintro a hi
    simp only [hi, mem_setOf_eq, Finset.mem_coe, iff_true, hX.meas_apply]
  rintro a
  by_cases a ∈ s
  · simp only [mem_setOf_eq, Finset.mem_coe, iff_true, *]
    exact ⟨{True}, trivial, by simp⟩
  · simp only [mem_setOf_eq, Finset.mem_coe, iff_false, *]
    exact ⟨{False}, trivial, by simp⟩

protected lemma meas_subset [IsProbabilityMeasure μ] [Fintype α] (s : Finset α) :
    μ {ω | ∀ x ∈ s, x ∈ X ω} = p ^ #s := by
classical
simp_rw [setOf_forall]
rw [hX.iIndepFun.meas_iInter, ← s.prod_mul_prod_compl, Finset.prod_eq_pow_card,
  Finset.prod_eq_pow_card, Finset.card_compl]
pick_goal 4
· rintro a hi
  simp [hi, mem_setOf_eq, Finset.mem_coe, iff_true, hX.meas_apply]
  rfl
pick_goal 2
· rintro a hi
  rw [Finset.mem_compl] at hi
  simp [hi, ← compl_setOf, prob_compl_eq_one_sub₀, mem_setOf_eq, Finset.mem_coe,
    iff_false, hX.nullMeasurableSet, hX.meas_apply]
  rfl
. simp
. rintro a
  by_cases hi : a ∈ s
  · simp only [mem_setOf_eq, Finset.mem_coe, iff_true, *]
    exact ⟨{True}, trivial, by simp⟩
  · simp only [mem_setOf_eq, Finset.mem_coe, iff_false, *]
    exact ⟨univ, trivial, by simp⟩

protected lemma meas_ne_subset [IsProbabilityMeasure μ] [Fintype α] (s : Finset α) :
    μ {ω | ∀ x ∈ s, x ∉ X ω} = (1-p) ^ #s := by
classical
simp_rw [setOf_forall]
rw [hX.iIndepFun.meas_iInter, ← s.prod_mul_prod_compl, Finset.prod_eq_pow_card,
  Finset.prod_eq_pow_card, Finset.card_compl]
pick_goal 4
· rintro a hi
  simp [hi, mem_setOf_eq, Finset.mem_coe, iff_true, hX.meas_apply']
  rfl
pick_goal 2
· rintro a hi
  rw [Finset.mem_compl] at hi
  simp [hi, ← compl_setOf, prob_compl_eq_one_sub₀, mem_setOf_eq, Finset.mem_coe,
    iff_false, hX.nullMeasurableSet, hX.meas_apply]
  rfl
. simp
. rintro a
  by_cases hi : a ∈ s
  · simp only [mem_setOf_eq, Finset.mem_coe, iff_true, *]
    exact ⟨{False}, trivial, by simp⟩
  · simp only [mem_setOf_eq, Finset.mem_coe, iff_false, *]
    exact ⟨univ, trivial, by simp⟩

/-- The complement of a sequence of independent `p`-Bernoulli random variables is a sequence of
independent `1 - p`-Bernoulli random variables. -/
lemma compl : IsBernoulliSeq (fun ω ↦ (X ω)ᶜ) (1 - p) μ where
  le_one := tsub_le_self
  iIndepFun := by
    simp only [iIndepFun_iff, mem_compl_iff, MeasurableSpace.comap_not]
    exact (iIndepFun_iff _ _ _).1 hX.iIndepFun
  map a := by
    have : Measurable Not := fun _ _ ↦ trivial
    refine (this.aemeasurable.map_map_of_aemeasurable (hX.aemeasurable _)).symm.trans ?_
    rw [hX.map, PMF.toMeasure_map _ _ this, PMF.map_not_bernoulli']

include hY

protected lemma aemeasurable_inter(a : α) : AEMeasurable (fun ω ↦ a ∈ X ω ∩ Y ω) μ := by
  obtain ⟨XX, m_XX, gx⟩:= hX.aemeasurable a
  obtain ⟨YY, m_YY, gy⟩:= hY.aemeasurable a
  use (fun x => XX x /\ YY x)
  constructor
  . apply Measurable.setOf at m_XX
    apply Measurable.setOf at m_YY
    have h := MeasurableSet.inter m_XX m_YY
    rw [← measurable_mem] at h
    exact h
  . unfold Filter.EventuallyEq Filter.Eventually at gx gy
    unfold Filter.EventuallyEq Filter.Eventually
    simp at gx gy
    simp
    have h := Filter.inter_sets _ gx gy
    apply Filter.sets_of_superset _ h ?_
    rw [← Set.setOf_and, Set.setOf_subset_setOf]
    tauto

variable [IsProbabilityMeasure (μ : Measure Ω)]

/-- The intersection of a sequence of independent `p`-Bernoulli and `q`-Bernoulli random variables
is a sequence of independent `p * q`-Bernoulli random variables. -/
protected lemma inter (h : IndepFun X Y μ) : IsBernoulliSeq (fun ω ↦ X ω ∩ Y ω) (p * q) μ where
  le_one := mul_le_one' hX.le_one hY.le_one
  iIndepFun := by
    rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
    intros S sets h_sets
    by_cases g: ∀ i ∈ S, @MeasurableSet Ω (MeasurableSpace.comap (fun ω ↦ i ∈ X ω) inferInstance) ((fun ω ↦ i ∈ X ω ∩ Y ω) ⁻¹' sets i)
    . apply iIndepFun.meas_biInter
      exact hX.iIndepFun
      exact g
    . simp at g
      obtain ⟨j, hj, g⟩ := g
      specialize h_sets j hj
      exfalso
      apply g
      sorry
    /-
    have : ∀ i ∈ S,  ((fun ω ↦ i ∈ X ω ∩ Y ω) ⁻¹' sets i) ⊆ ((fun ω => i ∈ X ω) ⁻¹' sets i) := by
      intros i hi
      specialize h_sets i hi
      rw [Set.preimage_subset_iff]
      intros a ha
      rw [Set.mem_preimage]
      sorry
    -/
    -- rw [IndepFun_iff] at h
    -- have g := hX.iIndepFun
    -- rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at g
    all_goals sorry
  /-
    refine ((iIndepSet_iff_meas_biInter fun i ↦ ?_).2 ?_).iIndep_comap_mem
    . refine MeasurableSet.inter ?_ ?_
      . sorry -- needs refactor of `Probability.Independence.Basic`
      . sorry -- needs refactor of `Probability.Independence.Basic`
    . refine fun s ↦ ?_
      -- We abused defeq using `iIndepSet.Indep_comap`, so we fix it here
      change μ (⋂ i ∈ s, {ω | X ω i} ∩ {ω | Y ω i}) = s.prod fun i ↦ μ ({ω | X ω i} ∩ {ω | Y ω i})
      simp_rw [iInter_inter_distrib]
      rw [h.meas_inter, hX.iIndepFun.meas_biInter, hY.iIndepFun.meas_biInter,
        ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i hi ↦ (h.meas_inter ?_ ?_).symm
      . sorry -- needs refactor of `Probability.Independence.Basic`
      . sorry -- needs refactor of `Probability.Independence.Basic`
      . sorry -- needs refactor of `Probability.Independence.Basic`
      . sorry -- needs refactor of `Probability.Independence.Basic`
      . sorry -- needs refactor of `Probability.Independence.Basic`
      . sorry -- needs refactor of `Probability.Independence.Basic`
  -/
  map a := by
    ext sp msp
    simp only [Measure.map]
    split_ifs with hae
    . unfold Measure.mapₗ
      split_ifs with hf
      . simp
        let ssa : Set (Set α) := {s | a ∈ s}
        let sx := (fun ω => X ω) ⁻¹' ssa
        let sy := (fun ω => Y ω) ⁻¹' ssa
        let sxy := (fun ω => X ω ∩ Y ω) ⁻¹' ssa
        have g : μ (AEMeasurable.mk (fun ω ↦ a ∈ X ω ∩ Y ω) hae ⁻¹' {True}) = p*q := by
          simp [preimage]
          sorry
        unfold Set.indicator
        split_ifs <;> simp
        . have : sp = {True, False} := by
            apply Set.eq_of_subset_of_subset <;> intros x hx <;> by_cases x <;> simp_all
          subst sp
          rw [← univ_eq_true_false, Set.preimage_univ]
          simp
          norm_cast
          rw [← (add_tsub_assoc_of_le (mul_le_one' hX.le_one hY.le_one))]
          rw [← tsub_add_eq_add_tsub]
          all_goals norm_num
        . have : sp = {True} := by
            apply Set.eq_of_subset_of_subset <;> intros x hx <;> by_cases x <;> simp_all
          subst sp
          exact g
        . have : sp = {False} := by
            apply Set.eq_of_subset_of_subset <;> intros x hx <;> by_cases x <;> simp_all
          subst sp
          have h : False = ¬ True := by simp
          rw [h, ← Prop.compl_singleton True, Set.preimage_compl, ← g, MeasureTheory.prob_compl_eq_one_sub]
          apply AEMeasurable.measurable_mk
          apply MeasurableSpace.measurableSet_top
        . have : sp = ∅ := by
            apply Set.eq_of_subset_of_subset <;> intros x hx
            . by_cases x <;> simp_all
            . simp_all
          subst sp
          rw [preimage_empty]
          simp
        /-
        rw [IndepFun_iff] at h
        -- rw [ProbabilityTheory.indepFun_iff_indepSet_preimage] at h
        have : μ sx = p := by
          unfold sx ssa
          simp
          apply hX.meas_apply
        have : μ sy = q := by
          unfold sy ssa
          simp
          apply hY.meas_apply
        have : μ sxy = p * q := by
          unfold sxy ssa
          simp
          rw [Set.setOf_and]
          rw [h]
          rw [hX.meas_apply, hY.meas_apply]
          . have h : @MeasurableSet Ω (MeasurableSpace.comap X instMeasurableSpace) sx := by
              unfold sx ssa
              apply MeasurableSet.preimage
              pick_goal 3
              exact ⊤
              all_goals sorry
            exact h
          all_goals sorry
        all_goals sorry
        -/
      . exfalso
        apply hf
        apply AEMeasurable.measurable_mk
    . exfalso
      apply hae
      apply hX.aemeasurable_inter hY


/-- The union of a sequence of independent `p`-Bernoulli random variables and `q`-Bernoulli random
variables is a sequence of independent `p + q - p * q`-Bernoulli random variables. -/
protected lemma union (h : IndepFun X Y μ) :
    IsBernoulliSeq (fun ω ↦ X ω ∪ Y ω) (p + q - p * q) μ := by
  convert (hX.compl.inter hY.compl _).compl using 1
  · simp [compl_inter]
  · rw [mul_tsub, mul_one, tsub_tsub, tsub_tsub_cancel_of_le, tsub_mul, one_mul,
      add_tsub_assoc_of_le (mul_le_of_le_one_left' hX.le_one)]
    · exact (add_le_add_left (mul_le_of_le_one_right' hY.le_one) _).trans_eq
        (add_tsub_cancel_of_le hX.le_one)
  · rwa [IndepFun_iff, MeasurableSpace.comap_compl measurable_compl,
      MeasurableSpace.comap_compl measurable_compl, ← IndepFun_iff]

end IsBernoulliSeq
end ProbabilityTheory
