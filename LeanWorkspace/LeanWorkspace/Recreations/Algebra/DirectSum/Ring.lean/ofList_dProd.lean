import Mathlib

open scoped DirectSum

variable {ι : Type*} [DecidableEq ι]

variable (A : ι → Type*)

variable [∀ i, AddCommMonoid (A i)] [AddMonoid ι] [GSemiring A]

private theorem mul_assoc (a b c : ⨁ i, A i) : a * b * c = a * (b * c) := by
  -- (`fun a b c => a * b * c` as a bundled hom) = (`fun a b c => a * (b * c)` as a bundled hom)
  suffices AddMonoidHom.mulLeft₃ = AddMonoidHom.mulRight₃ by
      simpa only [AddMonoidHom.mulLeft₃_apply, AddMonoidHom.mulRight₃_apply] using
        DFunLike.congr_fun (DFunLike.congr_fun (DFunLike.congr_fun this a) b) c
  ext ai ax bi bx ci cx : 6
  dsimp only [coe_comp, Function.comp_apply, AddMonoidHom.mulLeft₃_apply,
    AddMonoidHom.mulRight₃_apply]
  simp_rw [DirectSum.of_mul_of]
  exact DirectSum.of_eq_of_gradedMonoid_eq (_root_.mul_assoc (GradedMonoid.mk ai ax) ⟨bi, bx⟩ ⟨ci, cx⟩)


theorem ofList_dProd {α} (l : List α) (fι : α → ι) (fA : ∀ a, A (fι a)) :
    of A _ (l.dProd fι fA) = (l.map fun a => of A (fι a) (fA a)).prod := by
  induction l with
  | nil => simp only [List.map_nil, List.prod_nil, List.dProd_nil]; rfl
  | cons head tail =>
    rename_i ih
    simp only [List.map_cons, List.prod_cons, List.dProd_cons, ← ih]
    rw [DirectSum.of_mul_of (fA head)]
    rfl

