import Mathlib

variable {ι κ M R : Type*} {s s₁ s₂ : Finset ι} {i : ι}

variable [NonUnitalSemiring R] {f : ι → R} {a : R}

theorem dvd_sum (h : ∀ i ∈ s, a ∣ f i) : a ∣ ∑ i ∈ s, f i := Multiset.dvd_sum fun y hy => by rcases Multiset.mem_map.1 hy with ⟨x, hx, rfl⟩; exact h x hx

