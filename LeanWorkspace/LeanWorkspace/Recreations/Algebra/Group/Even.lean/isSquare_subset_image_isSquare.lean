import Mathlib

variable {F α β : Type*}

variable [MulOneClass α] [MulOneClass β] [FunLike F α β] [MonoidHomClass F α β]

theorem isSquare_subset_image_isSquare {f : F} (hf : Function.Surjective f) :
    {b | IsSquare b} ⊆ f '' {a | IsSquare a} := fun b ⟨s, _⟩ => by
  rcases hf s with ⟨r, rfl⟩
  exact ⟨r * r, by simp [*]⟩

