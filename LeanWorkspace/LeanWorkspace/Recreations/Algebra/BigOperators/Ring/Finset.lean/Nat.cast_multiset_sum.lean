import Mathlib

variable {ι κ M R : Type*} {s s₁ s₂ : Finset ι} {i : ι}

variable {ι : Type*} {s : Finset ι} {f : ι → ℕ} {n : ℕ}

theorem cast_multiset_sum [AddCommMonoidWithOne R] (s : Multiset ℕ) :
    (↑s.sum : R) = (s.map (↑)).sum := map_multiset_sum (castAddMonoidHom R) _

