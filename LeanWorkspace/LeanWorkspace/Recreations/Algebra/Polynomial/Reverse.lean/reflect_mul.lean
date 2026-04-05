import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

theorem reflect_mul (f g : R[X]) {F G : ℕ} (Ff : f.natDegree ≤ F) (Gg : g.natDegree ≤ G) :
    Polynomial.reflect (F + G) (f * g) = Polynomial.reflect F f * Polynomial.reflect G g := Polynomial.reflect_mul_induction _ _ F G f g f.support.card.le_succ g.support.card.le_succ Ff Gg

