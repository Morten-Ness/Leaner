import Mathlib

variable {R : Type*}

private theorem Submonoid.square_subsemiringClosure {T : Type*} [CommSemiring T] :
    (Submonoid.square T).subsemiringClosure = .closure {x : T | IsSquare x} := by
  simp [Submonoid.subsemiringClosure_eq_closure]


theorem IsSumSq.nonneg {R : Type*} [Semiring R] [LinearOrder R] [IsStrictOrderedRing R]
    [ExistsAddOfLE R] {s : R} (hs : IsSumSq s) : 0 ≤ s := by
  induction hs using IsSumSq.rec' with
  | zero          => simp
  | sq_add hx _ h => exact add_nonneg (IsSquare.nonneg hx) h

