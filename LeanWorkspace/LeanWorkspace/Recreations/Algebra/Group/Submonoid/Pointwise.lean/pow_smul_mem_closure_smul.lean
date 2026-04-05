import Mathlib

variable {α G M R A S : Type*}

variable [Monoid M] [AddMonoid A]

variable {s t u : Set M}

theorem pow_smul_mem_closure_smul {N : Type*} [CommMonoid N] [MulAction M N] [IsScalarTower M N N]
    (r : M) (s : Set N) {x : N} (hx : x ∈ closure s) : ∃ n : ℕ, r ^ n • x ∈ closure (r • s) := by
  induction hx using closure_induction with
  | mem x hx => exact ⟨1, subset_closure ⟨_, hx, by rw [pow_one]⟩⟩
  | one => exact ⟨0, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨⟨nx, hx⟩, ⟨ny, hy⟩⟩ := And.intro hx hy
    use ny + nx
    rw [pow_add, mul_smul, ← smul_mul_assoc, mul_comm, ← smul_mul_assoc]
    exact mul_mem hy hx

