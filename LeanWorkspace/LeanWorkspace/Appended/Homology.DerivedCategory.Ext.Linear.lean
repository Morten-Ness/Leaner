import Mathlib

section

variable {R : Type t} [Ring R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  [HasExt.{w} C]

variable {X Y : C} {n : ℕ}

theorem comp_smul {X Y Z : C} {a b : ℕ} (α : CategoryTheory.Abelian.Ext X Y a) (β : CategoryTheory.Abelian.Ext Y Z b)
    {c : ℕ} (h : a + b = c) (r : R) :
    α.comp (r • β) h = r • α.comp β h := by
  let := HasDerivedCategory.standard C
  aesop

end

section

variable {R : Type t} [Ring R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  [HasExt.{w} C]

variable {X Y : C} {n : ℕ}

theorem mk₀_linearEquiv₀_apply (f : CategoryTheory.Abelian.Ext X Y 0) :
    mk₀ (CategoryTheory.Abelian.Ext.linearEquiv₀ (R := R) f) = f :=
  addEquiv₀.left_inv f

end

section

variable {R : Type t} [Ring R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  [HasExt.{w} C]

variable {X Y : C} {n : ℕ}

theorem mk₀_smul (r : R) (f : X ⟶ Y) : mk₀ (r • f) = r • mk₀ f := by
  let := HasDerivedCategory.standard C
  aesop

end

section

variable {R : Type t} [Ring R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  [HasExt.{w} C]

variable {X Y : C} {n : ℕ}

theorem smul_comp {X Y Z : C} {a b : ℕ} (α : CategoryTheory.Abelian.Ext X Y a) (β : CategoryTheory.Abelian.Ext Y Z b)
    {c : ℕ} (h : a + b = c) (r : R) :
    (r • α).comp β h = r • α.comp β h := by
  let := HasDerivedCategory.standard C
  aesop

end

section

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

end

section

variable {R : Type t} [Ring R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  [HasExt.{w} C]

variable {X Y : C} {n : ℕ}

theorem smul_hom (x : CategoryTheory.Abelian.Ext X Y n) (r : R) [HasDerivedCategory C] :
    (r • x).hom = r • x.hom := by
  simp [CategoryTheory.Abelian.Ext.smul_eq_comp_mk₀]

end
