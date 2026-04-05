import Mathlib

variable {R : Type uR} {S : Type uS} {ι : Type uι} {n : ℕ}
  {M : Fin n.succ → Type v} {M₁ : ι → Type v₁} {M₁' : ι → Type v₁'} {M₁'' : ι → Type v₁''}

variable {M₂ : Type v₂} {M₃ : Type v₃} {M₄ : Type v₄} {M' : Type v'}

variable [Semiring R] [∀ i, AddCommGroup (M₁ i)] [AddCommGroup M₂] [∀ i, Module R (M₁ i)]
  [Module R M₂] (f : MultilinearMap R M₁ M₂)

theorem map_sub_map_piecewise [LinearOrder ι] (a b : (i : ι) → M₁ i) (s : Finset ι) :
    f a - f (s.piecewise b a) =
    ∑ i ∈ s, f (fun j ↦ if j ∈ s → j < i then a j else if i = j then a j - b j else b j) := by
  induction s using induction_on_min with
  | empty => rw [Finset.piecewise_empty, sum_empty, sub_self]
  | insert k s hk ih => ?_
  rw [Finset.piecewise_insert, MultilinearMap.map_update, ← sub_add, ih,
      add_comm, sum_insert (lt_irrefl _ <| hk k ·)]
  simp_rw [s.mem_insert]
  congr 1
  · congr; MultilinearMap.ext i; split_ifs with h₁ h₂
    · rw [update_of_ne, Finset.piecewise_eq_of_notMem]
      · exact fun h ↦ (hk i h).not_gt (h₁ <| .inr h)
      · exact fun h ↦ (h₁ <| .inl h).ne h
    · cases h₂
      rw [Function.update_self, s.piecewise_eq_of_notMem _ _ (lt_irrefl _ <| hk k ·)]
    · push Not at h₁
      rw [update_of_ne (Ne.symm h₂), s.piecewise_eq_of_mem _ _ (h₁.1.resolve_left <| Ne.symm h₂)]
  · apply sum_congr rfl
    grind

