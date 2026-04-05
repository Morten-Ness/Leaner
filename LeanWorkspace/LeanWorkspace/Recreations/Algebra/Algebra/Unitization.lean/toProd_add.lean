import Mathlib

variable {T : Type*} {S : Type*} {R : Type*} {A : Type*}

theorem toProd_add [Add R] [Add A] (x₁ x₂ : Unitization R A) :
    (x₁ + x₂).toProd = x₁.toProd + x₂.toProd := rfl

