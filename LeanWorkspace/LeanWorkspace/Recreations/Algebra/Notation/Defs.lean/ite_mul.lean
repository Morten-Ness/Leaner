import Mathlib

variable {G : Type*}

variable {α : Type*} (P : Prop) [Decidable P]

variable [Mul α]

theorem ite_mul (a b c : α) : (if P then a else b) * c = if P then a * c else b * c := dite_mul ..

-- We make `mul_ite` and `ite_mul` simp lemmas, but not `add_ite` or `ite_add`.
-- The problem we're trying to avoid is dealing with sums of the form `∑ x ∈ s, (f x + ite P 1 0)`,
-- in which `add_ite` followed by `sum_ite` would needlessly slice up
-- the `f x` terms according to whether `P` holds at `x`.
-- There doesn't appear to be a corresponding difficulty so far with `mul_ite` and `ite_mul`.
attribute [simp] mul_dite dite_mul mul_ite ite_mul

