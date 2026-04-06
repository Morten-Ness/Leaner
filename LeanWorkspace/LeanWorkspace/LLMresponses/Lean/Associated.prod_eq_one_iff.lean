FAIL
import Mathlib

variable {ι M M₀ : Type*}

variable [CommMonoid M]

theorem prod_eq_one_iff {p : Multiset (Associates M)} :
    p.prod = 1 ↔ ∀ a ∈ p, (a : Associates M) = 1 := by
  classical
  induction p using Multiset.induction_on with
  | empty =>
      simp
  | @cons a p ih =>
      constructor
      · intro h
        intro b hb
        rcases Multiset.mem_cons.mp hb with rfl | hb
        · have h' : a * p.prod = (1 : Associates M) := by
            simpa using h
          rw [show p.prod = (1 : Associates M) by
            have hp : ∀ c ∈ p, (c : Associates M) = 1 := by
              intro c hc
              exact ih.mp ?_ c hc
            · exact hp]
          simpa using h'
        · have hp1 : p.prod = 1 := by
            apply ih.mpr
            intro c hc
            have hc' : c ∈ a ::ₘ p := by
              exact Multiset.mem_cons_of_mem hc
            exact h c hc'
          exact ih.mp hp1 b hb
      · intro h
        have ha : a = (1 : Associates M) := h a (by simp)
        have hp : ∀ b ∈ p, (b : Associates M) = 1 := by
          intro b hb
          exact h b (Multiset.mem_cons_of_mem hb)
        have hp1 : p.prod = 1 := ih.mpr hp
        simp [ha, hp1]
