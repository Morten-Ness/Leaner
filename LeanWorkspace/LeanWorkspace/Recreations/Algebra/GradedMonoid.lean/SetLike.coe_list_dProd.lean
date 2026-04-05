import Mathlib

variable {ι : Type*}

variable {R : Type*}

variable {α S : Type*} [SetLike S R] [Monoid R] [AddMonoid ι]

theorem SetLike.coe_list_dProd (A : ι → S) [SetLike.GradedMonoid A] (fι : α → ι)
    (fA : ∀ a, A (fι a)) (l : List α) : ↑(@List.dProd _ _ (fun i => ↥(A i)) _ _ l fι fA)
    = (List.prod (l.map fun a => fA a) : R) := by
  match l with
  | [] =>
    rw [List.dProd_nil, coe_gOne, List.map_nil, List.prod_nil]
  | head::tail =>
    rw [List.dProd_cons, coe_gMul, List.map_cons, List.prod_cons,
      SetLike.coe_list_dProd _ _ _ tail]

