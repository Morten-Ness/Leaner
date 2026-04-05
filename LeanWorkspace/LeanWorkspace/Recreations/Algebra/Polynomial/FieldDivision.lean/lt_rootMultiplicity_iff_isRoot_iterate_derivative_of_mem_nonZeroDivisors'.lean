import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {k : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R]

theorem lt_rootMultiplicity_iff_isRoot_iterate_derivative_of_mem_nonZeroDivisors'
    {p : R[X]} {t : R} {n : ℕ} (h : p ≠ 0)
    (hnzd : ∀ m ≤ n, m ≠ 0 → (m : R) ∈ nonZeroDivisors R) :
    n < p.rootMultiplicity t ↔ ∀ m ≤ n, (derivative^[m] p).IsRoot t := ⟨fun hn _ hm ↦ Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity <| Nat.lt_of_le_of_lt hm hn,
    fun hr ↦ Polynomial.lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors' h hr hnzd⟩

