import Mathlib

variable {R M M' N N' P P' : Type*}

variable (f : M → N) (g : N → P) (g' : P → P')

theorem comp_injective [One P] [One P'] (mulExact : Function.MulExact f g)
    (inj : Function.Injective g') (h0 : g' 1 = 1) :
    Function.MulExact f (g' ∘ g) := by
  intro x
  refine ⟨fun H => mulExact x |>.mp <| inj <| h0 ▸ H, ?_⟩
  intro H
  rw [Function.comp_apply, mulExact x |>.mpr H, h0]

