FAIL
import Mathlib

variable (ι : Type v) (β : ι → Type w)

variable [∀ i, AddCommMonoid (β i)]

variable {M S : Type*} [AddCommMonoid M] [SetLike S M] [AddSubmonoidClass S M]

variable {ι : Type*} {α : ι → Type*} {β : ι → Type*} [∀ i, AddCommMonoid (α i)]

variable [∀ i, AddCommMonoid (β i)] (f : ∀ (i : ι), α i →+ β i)

theorem map_surjective : Function.Surjective (DirectSum.map f) ↔ (∀ i, Function.Surjective (f i)) := by
  classical
  constructor
  · intro h i
    simpa [Function.Surjective] using
      (DirectSum.addHom_ext fun x =>
        h.comp (DirectSum.of α i)).surjective
  · intro h
    intro x
    refine DirectSum.induction_on x ?_ ?_ ?_
    · exact ⟨0, by simp⟩
    · intro i y
      rcases h i y with ⟨x, rfl⟩
      exact ⟨DirectSum.of α i x, by simp [DirectSum.map_of]⟩
    · intro x y hx hy
      rcases hx with ⟨x', rfl⟩
      rcases hy with ⟨y', rfl⟩
      exact ⟨x' + y', by simp⟩
