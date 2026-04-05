import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroObject C]

variable [HasZeroMorphisms C] (K L M : HomologicalComplex C c)
  (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

set_option backward.isDefEq.respectTransparency false in
theorem XOpIso_hom_d_op (i j : Option ι) :
    (HomologicalComplex.extend.XOpIso K i).hom ≫ (HomologicalComplex.extend.d K j i).op =
      HomologicalComplex.extend.d K.op i j ≫ (HomologicalComplex.extend.XOpIso K j).hom := match i, j with
  | none, _ => by
      simp only [HomologicalComplex.extend.d_none_eq_zero, HomologicalComplex.extend.d_none_eq_zero', comp_zero, zero_comp, op_zero]
  | some i, some j => by
      dsimp [HomologicalComplex.extend.XOpIso]
      simp only [HomologicalComplex.extend.d_eq _ rfl rfl, op_comp, assoc, id_comp, comp_id]
      rfl
  | some _, none => by
      simp only [HomologicalComplex.extend.d_none_eq_zero, HomologicalComplex.extend.d_none_eq_zero', comp_zero, zero_comp, op_zero]

