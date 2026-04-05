import Mathlib

variable {ι α β F : Type*} [FunLike F α β]

variable [Monoid α] [Monoid β] [MonoidHomClass F α β]

theorem image_list_prod (f : F) :
    ∀ l : List (Set α), (f : α → β) '' l.prod = (l.map fun s => f '' s).prod
  | [] => image_one.trans <| congr_arg singleton (map_one f)
  | a :: as => by rw [List.map_cons, List.prod_cons, List.prod_cons, image_mul, image_list_prod _ _]
