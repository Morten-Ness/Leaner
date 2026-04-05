import Mathlib

variable {A : Type u} [Ring A] {ι : Type w} [DecidableEq ι]
  (relations : ι → Relations.{w₀, w₁} A)
  {M : ι → Type v} [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]

variable {N : Type v} [AddCommGroup N] [Module A N]

theorem directSum_var (solution : ∀ (i : ι), (relations i).Solution (M i))
    (i : ι) (g : (relations i).G) :
    (Module.Relations.Solution.directSum solution).var ⟨i, g⟩ = DirectSum.lof A ι M i ((solution i).var g) := rfl

