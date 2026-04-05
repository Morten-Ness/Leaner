import Mathlib

variable {ι α β F : Type*} [FunLike F α β]

variable [CommMonoid α] [CommMonoid β] [MonoidHomClass F α β]

theorem list_prod_mem_list_prod (t : List ι) (f : ι → Set α) (g : ι → α) (hg : ∀ i ∈ t, g i ∈ f i) :
    (t.map g).prod ∈ (t.map f).prod := by
  induction t with
  | nil => simp_rw [List.map_nil, List.prod_nil, Set.mem_one]
  | cons h tl ih =>
    simp_rw [List.map_cons, List.prod_cons]
    exact mul_mem_mul (hg h List.mem_cons_self)
      (ih fun i hi ↦ hg i <| List.mem_cons_of_mem _ hi)

