import Mathlib

variable {M : Type*} [CommMonoid M] {ι : Type*} (f : ι → M) (x : M)

theorem mem_closure_finset' {s : Finset M} :
    x ∈ closure s ↔ ∃ a : s → ℕ, x = ∏ i : s, i.1 ^ a i := Submonoid.mem_closure_iff_of_fintype

