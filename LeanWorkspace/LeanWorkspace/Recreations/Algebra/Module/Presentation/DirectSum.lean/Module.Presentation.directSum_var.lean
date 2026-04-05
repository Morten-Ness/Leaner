import Mathlib

variable {A : Type u} [Ring A] {ι : Type w} [DecidableEq ι]
  (relations : ι → Relations.{w₀, w₁} A)
  {M : ι → Type v} [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]

theorem directSum_var (pres : ∀ (i : ι), Module.Presentation A (M i)) (i : ι) (g : (pres i).G) :
    (Module.Presentation.directSum pres).var ⟨i, g⟩ = DirectSum.lof A ι M i ((pres i).var g) := rfl

