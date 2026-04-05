import Mathlib

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M]

theorem prod_dite {s : Finset ι} {p : ι → Prop} [DecidablePred p] (f : ∀ x : ι, p x → M)
    (g : ∀ x : ι, ¬p x → M) :
    ∏ x ∈ s, (if hx : p x then f x hx else g x hx) =
      (∏ x : {x ∈ s | p x}, f x.1 (by simpa using (mem_filter.mp x.2).2)) *
        ∏ x : {x ∈ s | ¬p x}, g x.1 (by simpa using (mem_filter.mp x.2).2) := by
  simp [Finset.prod_apply_dite _ _ fun x => x]

