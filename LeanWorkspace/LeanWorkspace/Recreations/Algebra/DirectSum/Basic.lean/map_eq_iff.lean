import Mathlib

variable (ι : Type v) (β : ι → Type w)

variable [∀ i, AddCommMonoid (β i)]

variable {M S : Type*} [AddCommMonoid M] [SetLike S M] [AddSubmonoidClass S M]

variable {ι : Type*} {α : ι → Type*} {β : ι → Type*} [∀ i, AddCommMonoid (α i)]

variable [∀ i, AddCommMonoid (β i)] (f : ∀ (i : ι), α i →+ β i)

theorem map_eq_iff (x y : ⨁ i, α i) :
    DirectSum.map f x = DirectSum.map f y ↔ ∀ i, f i (x i) = f i (y i) := by
  simp_rw [DirectSum.ext_iff, map_apply]

