import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

variable (f : R →+* S) (x : S)

variable [Semiring T]

theorem eval₂_sum (p : T[X]) (g : ℕ → T → R[X]) (x : S) :
    (p.sum g).eval₂ f x = p.sum fun n a => (g n a).eval₂ f x := by
  let T : R[X] →+ S :=
    { toFun := eval₂ f x
      map_zero' := Polynomial.eval₂_zero _ _
      map_add' := fun p q => Polynomial.eval₂_add _ _ }
  have A : ∀ y, eval₂ f x y = T y := fun y => rfl
  simp only [A]
  rw [sum, map_sum, sum]

