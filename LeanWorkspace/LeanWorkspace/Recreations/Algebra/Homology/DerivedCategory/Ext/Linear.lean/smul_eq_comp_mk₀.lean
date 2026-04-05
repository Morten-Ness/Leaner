import Mathlib

variable {R : Type t} [Ring R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  [HasExt.{w} C]

variable {X Y : C} {n : ℕ}

theorem smul_eq_comp_mk₀ (x : CategoryTheory.Abelian.Ext X Y n) (r : R) :
    r • x = x.comp (mk₀ (r • 𝟙 Y)) (add_zero _) := by
  let := HasDerivedCategory.standard C
  ext
  apply ((Equiv.linearEquiv R homEquiv).map_smul r x).trans
  change r • homEquiv x = (x.comp (mk₀ (r • 𝟙 Y)) (add_zero _)).hom
  rw [comp_hom, mk₀_hom, Functor.map_smul, Functor.map_id, ShiftedHom.mk₀_smul,
    ShiftedHom.comp_smul, ShiftedHom.comp_mk₀_id]

