import Mathlib

variable {R M M' N N' P P' : Type*}

variable (f : M → N) (g : N → P) (g' : P → P')

theorem of_comp_of_mem_range [One P] (h1 : g ∘ f = 1)
    (h2 : ∀ x, g x = 1 → x ∈ Set.range f) : Function.MulExact f g := by
  rw [Function.MulExact]
  intro y
  constructor
  · intro hy
    exact h2 y hy
  · rintro ⟨x, rfl⟩
    exact congrFun h1 x
