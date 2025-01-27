import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Cycle

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {n : ℕ}

instance: Fintype { s : Cycle α // s.Nodup /\ s.length = n} :=
  Fintype.subtype
    (((Finset.univ : Finset { s : Cycle α // s.Nodup }).map (Function.Embedding.subtype _)).filter
      (fun x => x.length = n ))
    (by simp)

theorem ee : Fintype.card {s : Cycle α // s.Nodup /\ s.length = n} = Nat.factorial (Fintype.card α) / ((Nat.factorial (Fintype.card α - n)) * n) := by

sorry
