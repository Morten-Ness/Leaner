import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

theorem card_biUnion_le [DecidableEq M] {s : Finset ι} {t : ι → Finset M} :
    #(s.biUnion t) ≤ ∑ a ∈ s, #(t a) := haveI := Classical.decEq ι
  Finset.induction_on s (by simp) fun a s has ih =>
    calc
      #((insert a s).biUnion t) ≤ #(t a) + #(s.biUnion t) := by
        rw [biUnion_insert]; exact card_union_le ..
      _ ≤ ∑ a ∈ insert a s, #(t a) := by grind

