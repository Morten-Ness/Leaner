import Mathlib

variable {A B M N : Type*} [AddMonoid A] [AddMonoid B] [Monoid M] [Monoid N] {ψ : AddChar A M}

theorem compAddMonoidHom_injective_left (f : A →+ B) (hf : Function.Surjective f) :
    Function.Injective fun ψ : AddChar B M ↦ ψ.compAddMonoidHom f := by
  intro ψ₁ ψ₂ h
  ext b
  rcases hf b with ⟨a, rfl⟩
  exact congrArg (fun χ => χ a) h
