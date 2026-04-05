import Mathlib

variable {ι ι' R : Type*} [Ring R] {S : ShortComplex (ModuleCat R)}
  (hS : S.Exact) (hS' : S.ShortExact) {v : ι → S.X₁}

theorem free_shortExact_finrank_add {n p : ℕ} [Module.Free R S.X₁] [Module.Free R S.X₃]
    [Module.Finite R S.X₁] [Module.Finite R S.X₃]
    (hN : Module.finrank R S.X₁ = n)
    (hP : Module.finrank R S.X₃ = p)
    [StrongRankCondition R] :
    finrank R S.X₂ = n + p := by
  apply finrank_eq_of_rank_eq
  rw [ModuleCat.free_shortExact_rank_add hS', ← hN, ← hP]
  simp only [Nat.cast_add, finrank_eq_rank]

