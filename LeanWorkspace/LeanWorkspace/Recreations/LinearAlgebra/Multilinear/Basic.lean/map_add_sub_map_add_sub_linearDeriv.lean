import Mathlib

variable {R : Type uR} {S : Type uS} {ι : Type uι} {n : ℕ}
  {M : Fin n.succ → Type v} {M₁ : ι → Type v₁} {M₁' : ι → Type v₁'} {M₁'' : ι → Type v₁''}

variable {M₂ : Type v₂} {M₃ : Type v₃} {M₄ : Type v₄} {M' : Type v'}

variable [Semiring R] [∀ i, AddCommGroup (M₁ i)] [AddCommGroup M₂] [∀ i, Module R (M₁ i)]
  [Module R M₂] (f : MultilinearMap R M₁ M₂)

theorem map_add_sub_map_add_sub_linearDeriv [DecidableEq ι] [Fintype ι] (x h h' : (i : ι) → M₁ i) :
    f (x + h) - f (x + h') - f.linearDeriv x (h - h') =
    ∑ s with 2 ≤ #s, (f (s.piecewise h x) - f (s.piecewise h' x)) := by
  simp_rw [MultilinearMap.map_add_eq_map_add_linearDeriv_add, add_assoc, add_sub_add_comm, sub_self, zero_add,
    ← map_sub, add_sub_cancel_left, sum_sub_distrib]

