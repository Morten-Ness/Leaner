import Mathlib

variable {n m R : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommSemiring R]

variable (s : ℤˣ) (A B : Matrix n n R) (i j : n)

theorem mul_adjp_apply_ne (h : i ≠ j) : (A * Matrix.adjp 1 A) i j = (A * Matrix.adjp (-1) A) i j := by
  simp_rw [mul_apply, Matrix.adjp_apply, mul_sum, sum_sigma']
  let f : (Σ x : n, Equiv.Perm n) → (Σ x : n, Equiv.Perm n) := fun ⟨x, σ⟩ ↦ ⟨σ i, σ * swap i j⟩
  let t s : Finset (Σ x : n, Equiv.Perm n) := Finset.univ.sigma fun x ↦ (ofSign s).filter fun σ ↦ σ j = x
  have hf {s} : ∀ p ∈ t s, f (f p) = p := by
    intro ⟨x, σ⟩ hp
    rw [mem_sigma, mem_filter, mem_ofSign] at hp
    simp_rw [f, Equiv.Perm.mul_apply, swap_apply_left, hp.2.2, mul_swap_mul_self]
  refine sum_bij' (fun p _ ↦ f p) (fun p _ ↦ f p) ?_ ?_ hf hf ?_
  · intro ⟨x, σ⟩ hp
    rw [mem_sigma, mem_filter, mem_ofSign] at hp ⊢
    rw [Equiv.Perm.mul_apply, sign_mul, hp.2.1, sign_swap h, swap_apply_right]
    exact ⟨mem_univ (σ i), rfl, rfl⟩
  · intro ⟨x, σ⟩ hp
    rw [mem_sigma, mem_filter, mem_ofSign] at hp ⊢
    rw [Equiv.Perm.mul_apply, sign_mul, hp.2.1, sign_swap h, swap_apply_right]
    exact ⟨mem_univ (σ i), rfl, rfl⟩
  · intro ⟨x, σ⟩ hp
    rw [mem_sigma, mem_filter, mem_ofSign] at hp
    have key : ({j}ᶜ : Finset n) = disjUnion ({i} : Finset n) ({i, j} : Finset n)ᶜ (by simp) := by
      rw [singleton_disjUnion, cons_eq_insert, compl_insert, insert_erase]
      rwa [mem_compl, mem_singleton]
    simp_rw [key, prod_disjUnion, prod_singleton, f, Equiv.Perm.mul_apply, swap_apply_left, ← mul_assoc]
    rw [mul_comm (A i x) (A i (σ i)), hp.2.2]
    refine congr_arg _ (prod_congr rfl fun x hx ↦ ?_)
    rw [mem_compl, mem_insert, mem_singleton, not_or] at hx
    rw [swap_apply_of_ne_of_ne hx.1 hx.2]

