import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem Nat.cast_finprod' {R : Type*} [CommSemiring R] [CharZero R] (f : ι → ℕ) :
    (∏ᶠ (x : ι), f x : ℕ) = ∏ᶠ (x : ι), (f x : R) := by
  by_cases hf : f.HasFiniteMulSupport
  · exact map_finprod (Nat.castRingHom R) hf
  · have H : ¬ (fun i ↦ (f i : R)).HasFiniteMulSupport :=
      fun h ↦ hf <| h.of_comp cast_one cast_injective
    rw [finprod_of_not_hasFiniteMulSupport hf, finprod_of_not_hasFiniteMulSupport H, cast_one]

