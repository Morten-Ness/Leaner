FAIL
import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [DecidableEq β]

variable [Monoid α] {s t : Finset α} {a : α} {m n : ℕ}

theorem pow_subset_pow (hst : s ⊆ t) (ht : 1 ∈ t) (hmn : m ≤ n) : s ^ m ⊆ t ^ n := by
  intro x hx
  rcases Nat.exists_eq_add_of_le hmn with ⟨k, rfl⟩
  have hsm : s ^ m ⊆ t ^ m := by
    intro y hy
    induction m generalizing y with
    | zero =>
        simpa using hy
    | succ m ihm =>
        rw [pow_succ, pow_succ] at hy ⊢
        rcases Finset.mem_mul.mp hy with ⟨a, ha, b, hb, rfl⟩
        exact Finset.mem_mul.mpr ⟨a, hst ha, b, ihm hb, rfl⟩
  have hones : ({1} : Finset α) ⊆ t := by
    intro y hy
    rwa [Finset.mem_singleton] at hy
  have hk : ({1} : Finset α) ^ k ⊆ t ^ k := by
    intro y hy
    induction k generalizing y with
    | zero =>
        simpa using hy
    | succ k ih =>
        rw [pow_succ, pow_succ] at hy ⊢
        rcases Finset.mem_mul.mp hy with ⟨a, ha, b, hb, rfl⟩
        exact Finset.mem_mul.mpr ⟨a, hones ha, b, ih hb, rfl⟩
  have h1 : 1 ∈ ({1} : Finset α) ^ k := by
    induction k with
    | zero =>
        simp
    | succ k ih =>
        rw [pow_succ]
        exact Finset.mem_mul.mpr ⟨1, ih, 1, by simp, by simp⟩
  have hx' : x ∈ t ^ m := hsm hx
  have hmul : x * 1 ∈ t ^ m * t ^ k := Finset.mem_mul.mpr ⟨x, hx', 1, hk h1, by simp⟩
  simpa [pow_add] using hmul
