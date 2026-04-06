FAIL
import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_eq_ite [DecidableEq ι] {s : Finset ι} {f : ι → M} (a : ι)
    (h₀ : ∀ b ∈ s, b ≠ a → f b = 1) :
    ∏ x ∈ s, f x = if a ∈ s then f a else 1 := by
  classical
  by_cases ha : a ∈ s
  · rw [if_pos ha]
    classical
    refine Finset.induction_on s ?base ?step
    · simp at ha
    · intro b t hb ht
      by_cases hba : b = a
      · subst hba
        simp only [Finset.mem_insert, true_or] at ha
        simp [Finset.prod_insert, hb, ht, h₀, ha]
      · have hat : a ∈ t := by
          simp only [Finset.mem_insert, hba, false_or] at ha
          exact ha
        have h₀t : ∀ c ∈ t, c ≠ a → f c = 1 := by
          intro c hc hca
          exact h₀ c (Finset.mem_insert_of_mem hc) hca
        have hfa : f b = 1 := h₀ b (Finset.mem_insert_self b t) hba
        simp [Finset.prod_insert, hb, hfa, ht, hat, h₀t]
  · rw [if_neg ha]
    refine Finset.prod_eq_one ?_
    intro b hb
    exact h₀ b hb (fun h => ha (h ▸ hb))
