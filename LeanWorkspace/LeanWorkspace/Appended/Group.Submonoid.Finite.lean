import Mathlib

section

variable {η : Type*} {f : η → Type*} [∀ i, MulOneClass (f i)]

variable {S : Type*} [SetLike S (Π i, f i)] [SubmonoidClass S (Π i, f i)]

theorem pi_mem_of_mulSingle_mem [Finite η] [DecidableEq η] {H : S} (x : Π i, f i)
    (h : ∀ i, Pi.mulSingle i (x i) ∈ H) : x ∈ H := by
  cases nonempty_fintype η
  exact Submonoid.pi_mem_of_mulSingle_mem_aux Finset.univ x (by simp) fun i _ => h i

end

section

variable {η : Type*} {f : η → Type*} [∀ i, MulOneClass (f i)]

variable {S : Type*} [SetLike S (Π i, f i)] [SubmonoidClass S (Π i, f i)]

theorem pi_mem_of_mulSingle_mem_aux [DecidableEq η] (I : Finset η) {H : S} (x : Π i, f i)
    (h1 : ∀ i, i ∉ I → x i = 1) (h2 : ∀ i, i ∈ I → Pi.mulSingle i (x i) ∈ H) : x ∈ H := by
  induction I using Finset.induction_on generalizing x with
  | empty =>
    have : x = 1 := funext fun i => h1 i (Finset.notMem_empty i)
    exact this ▸ one_mem H
  | insert i I hnotMem ih =>
    have : x = Function.update x i 1 * Pi.mulSingle i (x i) := by
      ext j
      by_cases heq : j = i
      · subst heq
        simp
      · simp [heq]
    rw [this]
    clear this
    apply mul_mem (ih _ _ _) (by simp [h2]) <;> clear ih <;> intro j hj
    · by_cases heq : j = i
      · subst heq
        simp
      · simpa [heq] using h1 j (by simpa [heq] using hj)
    · have : j ≠ i := fun h => h ▸ hnotMem <| hj
      simp only [ne_eq, this, not_false_eq_true, Function.update_of_ne]
      exact h2 _ (Finset.mem_insert_of_mem hj)

end
