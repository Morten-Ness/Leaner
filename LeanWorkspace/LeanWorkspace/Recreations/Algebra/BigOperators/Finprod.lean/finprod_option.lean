import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem finprod_option {f : Option α → M} (hf : HasFiniteMulSupport (f ∘ some)) :
    ∏ᶠ o, f o = f none * ∏ᶠ a, f (some a) := by
  replace hf : (mulSupport f).Finite := by simpa [finite_option]
  convert finprod_mem_insert' f (show none ∉ Set.range Option.some by simp)
    (hf.subset inter_subset_right)
  · simp
  · rw [finprod_mem_range]
    exact Option.some_injective _

