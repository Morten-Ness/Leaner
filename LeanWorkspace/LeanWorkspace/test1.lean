import Mathlib

variable {A B M N : Type*} [AddMonoid A] [AddMonoid B] [Monoid M] [Monoid N]

theorem compAddMonoidHom_injective_left
    (f : A →+ B) (hf : Function.Surjective f) :
    Function.Injective (fun ψ : AddChar B M => ψ.compAddMonoidHom f) := by
  intro ψ₁ ψ₂ h
  ext b
  obtain ⟨a, rfl⟩ := hf b
  simpa using congrArg (fun χ : AddChar A M => χ a) h
