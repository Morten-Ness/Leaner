import Mathlib

variable {ι : Type*}

variable {R : Type*}

variable {α S : Type*} [SetLike S R] [Monoid R] [AddMonoid ι]

theorem SetLike.list_dProd_eq (A : ι → S) [SetLike.GradedMonoid A] (fι : α → ι) (fA : ∀ a, A (fι a))
    (l : List α) :
    (@List.dProd _ _ (fun i => ↥(A i)) _ _ l fι fA) =
      ⟨List.prod (l.map fun a => fA a),
        (l.dProdIndex_eq_map_sum fι).symm ▸
          SetLike.list_prod_map_mem_graded l _ _ fun i _ => (fA i).prop⟩ := Subtype.ext <| SetLike.coe_list_dProd _ _ _ _

