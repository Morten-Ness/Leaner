import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

variable {f : α → β} {a b : FreeMonoid α}

theorem map_surjective {f : α → β} : Function.Surjective (FreeMonoid.map f) ↔ Function.Surjective f := by
  constructor
  · intro fs d
    rcases fs (FreeMonoid.of d) with ⟨b, hb⟩
    induction b using FreeMonoid.inductionOn' with
    | one =>
      have H := congr_arg FreeMonoid.length hb
      simp only [FreeMonoid.length_one, FreeMonoid.length_of, Nat.zero_ne_one, map_one] at H
    | mul_of head _ _ =>
      simp only [map_mul, FreeMonoid.map_of] at hb
      use head
      have H := congr_arg FreeMonoid.length hb
      simp only [FreeMonoid.length_mul, FreeMonoid.length_of, add_eq_left, FreeMonoid.length_eq_zero] at H
      rw [H, mul_one] at hb
      exact FreeMonoid.of_injective hb
  intro fs d
  induction d using FreeMonoid.inductionOn' with
  | one => use 1; rfl
  | mul_of head tail ih =>
    specialize fs head
    rcases fs with ⟨a, rfl⟩
    rcases ih with ⟨b, rfl⟩
    use FreeMonoid.of a * b
    rfl

