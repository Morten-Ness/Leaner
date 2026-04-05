import Mathlib

section

variable {α : Type u} {β : Type v}

theorem Pi.mulSingle_multiplicativeOfAdd_eq {ι : Type*} [DecidableEq ι] {M : ι → Type*}
    [(i : ι) → AddMonoid (M i)] (i : ι) (a : M i) (j : ι) :
    Pi.mulSingle (M := fun i ↦ Multiplicative (M i)) i (.ofAdd a) j = .ofAdd (Pi.single i a j) := by
  rcases eq_or_ne j i with rfl | h
  · simp only [mulSingle_eq_same, single_eq_same]
  · simp only [mulSingle, ne_eq, h, not_false_eq_true, Function.update_of_ne, one_apply, single,
      zero_apply, ofAdd_zero]

end

section

variable {α : Type u} {β : Type v}

theorem Pi.single_additiveOfMul_eq {ι : Type*} [DecidableEq ι] {M : ι → Type*}
    [(i : ι) → Monoid (M i)] (i : ι) (a : M i) (j : ι) :
    Pi.single (M := fun i ↦ Additive (M i)) i (.ofMul a) j = .ofMul (Pi.mulSingle i a j) := by
  rcases eq_or_ne j i with rfl | h
  · simp only [mulSingle_eq_same, single_eq_same]
  · simp only [single, ne_eq, h, not_false_eq_true, Function.update_of_ne, zero_apply, mulSingle,
      one_apply, ofMul_one]

end
