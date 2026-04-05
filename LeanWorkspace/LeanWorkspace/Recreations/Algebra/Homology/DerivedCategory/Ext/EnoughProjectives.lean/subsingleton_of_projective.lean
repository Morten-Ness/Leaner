import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C]

theorem subsingleton_of_projective [HasExt.{w} C]
    (P Y : C) [Projective P] (n : ℕ) : Subsingleton (CategoryTheory.Abelian.Ext.{w} P Y (n + 1)) := subsingleton_of_forall_eq 0 CategoryTheory.Abelian.Ext.eq_zero_of_projective

