import Mathlib

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M]

theorem prod_apply_ite_of_false {p : ι → Prop} [DecidablePred p] (f g : ι → γ) (k : γ → M)
    (h : ∀ x ∈ s, ¬p x) : (∏ x ∈ s, k (if p x then f x else g x)) = ∏ x ∈ s, k (g x) := by
  simp_rw [apply_ite k]
  exact Finset.prod_ite_of_false h _ _

