import Mathlib

variable {ι α β F : Type*} [FunLike F α β]

variable [CommMonoid α] [CommMonoid β] [MonoidHomClass F α β]

theorem list_prod_subset_list_prod (t : List ι) (f₁ f₂ : ι → Set α) (hf : ∀ i ∈ t, f₁ i ⊆ f₂ i) :
    (t.map f₁).prod ⊆ (t.map f₂).prod := by
  induction t with
  | nil => rfl
  | cons h tl ih =>
    simp_rw [List.map_cons, List.prod_cons]
    exact mul_subset_mul (hf h List.mem_cons_self)
      (ih fun i hi ↦ hf i <| List.mem_cons_of_mem _ hi)

