import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C]

theorem subsingleton_of_injective [HasExt.{w} C]
    (X I : C) [Function.Injective I] (n : ℕ) : Subsingleton (CategoryTheory.Abelian.Ext.{w} X I (n + 1)) := subsingleton_of_forall_eq 0 CategoryTheory.Abelian.Ext.eq_zero_of_injective

