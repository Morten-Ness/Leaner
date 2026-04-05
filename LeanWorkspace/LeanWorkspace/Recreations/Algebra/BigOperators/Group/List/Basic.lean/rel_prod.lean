import Mathlib

open scoped Relator

variable {ι α β M N P G : Type*}

variable [Monoid M] [Monoid N] [Monoid P] {l l₁ l₂ : List M} {a : M}

theorem rel_prod {R : M → N → Prop} (h : R 1 1) (hf : (R ⇒ R ⇒ R) (· * ·) (· * ·)) :
    (Forall₂ R ⇒ R) prod prod := rel_foldr hf h

