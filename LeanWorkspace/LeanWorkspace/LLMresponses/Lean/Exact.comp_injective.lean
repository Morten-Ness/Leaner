import Mathlib

variable {R M M' N N' P P' : Type*}

variable (f : M → N) (g : N → P) (g' : P → P')

theorem comp_injective [One P] [One P'] (mulExact : Function.MulExact f g)
    (inj : Function.Injective g') (h0 : g' 1 = 1) :
    Function.MulExact f (g' ∘ g) := by
  intro x
  constructor
  · intro hx
    rcases mulExact x with ⟨h1, _⟩
    apply h1
    apply inj
    simpa [Function.comp, h0] using hx
  · intro hx
    rcases mulExact x with ⟨_, h2⟩
    simpa [Function.comp, h0] using congrArg g' (h2 hx)
