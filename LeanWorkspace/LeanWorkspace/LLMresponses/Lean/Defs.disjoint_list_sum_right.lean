FAIL
import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

theorem disjoint_list_sum_right {a : Multiset α} {l : List (Multiset α)} :
    Disjoint a l.sum ↔ ∀ b ∈ l, Disjoint a b := by
  induction l with
  | nil =>
      simp [Disjoint]
  | cons b l ih =>
      constructor
      · intro h
        constructor
        · intro x hxa hxb
          exact h hxa (le_add_right hxb)
        · intro c hc
          exact (ih.mp ?_) c hc
          intro x hxa hxl
          exact h hxa (le_add_left hxl)
      · intro h
        rcases h with ⟨hab, hl⟩
        intro x hxa hx
        rw [Multiset.le_iff_count] at hxa hx ⊢
        ext y
        have hxb : x ≤ b := by
          rw [Multiset.le_iff_count]
          intro z
          exact le_trans (hx z) (Nat.le_add_right _ _)
        have hxl : x ≤ l.sum := by
          rw [Multiset.le_iff_count]
          intro z
          exact le_trans (hx z) (Nat.le_add_left _ _)
        have hx0b := hab hxa hxb
        have hx0l := (ih.mpr hl) hxa hxl
        simpa [Multiset.le_zero] using hx0b
