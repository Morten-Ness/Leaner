import Mathlib

variable {ι α β F : Type*} [FunLike F α β]

variable [CommMonoid α] [CommMonoid β] [MonoidHomClass F α β]

theorem mem_finset_prod (t : Finset ι) (f : ι → Set α) (a : α) :
    (a ∈ ∏ i ∈ t, f i) ↔ ∃ (g : ι → α) (_ : ∀ {i}, i ∈ t → g i ∈ f i), ∏ i ∈ t, g i = a := by
  classical
    induction t using Finset.induction_on generalizing a with
    | empty =>
      simp_rw [Finset.prod_empty, Set.mem_one]
      exact ⟨fun h ↦ ⟨fun _ ↦ a, fun hi ↦ False.elim (Finset.notMem_empty _ hi), h.symm⟩,
        fun ⟨_, _, hf⟩ ↦ hf.symm⟩
    | insert i is hi ih => ?_
    rw [Finset.prod_insert hi, Set.mem_mul]
    simp_rw [Finset.prod_insert hi]
    simp_rw [ih]
    constructor
    · rintro ⟨x, y, hx, ⟨g, hg, rfl⟩, rfl⟩
      refine ⟨Function.update g i x, ?_, ?_⟩
      · intro j hj
        obtain rfl | hj := Finset.mem_insert.mp hj
        · rwa [Function.update_self]
        · rw [update_of_ne (ne_of_mem_of_not_mem hj hi)]
          exact hg hj
      · rw [Finset.prod_update_of_notMem hi, Function.update_self]
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g i, hg (is.mem_insert_self _), is.prod g,
        ⟨⟨g, fun hi ↦ hg (Finset.mem_insert_of_mem hi), rfl⟩, rfl⟩⟩

