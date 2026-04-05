import Mathlib

variable {ι κ M R : Type*} {s s₁ s₂ : Finset ι} {i : ι}

variable {ι : Type*} {s : Finset ι} {f : ι → ℕ} {n : ℕ}

theorem cast_sum [AddCommMonoidWithOne R] (s : Finset ι) (f : ι → ℕ) :
    ↑(∑ x ∈ s, f x : ℕ) = ∑ x ∈ s, (f x : R) := map_sum (castAddMonoidHom R) _ _

