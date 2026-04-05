import Mathlib

variable {R : Type*}

private theorem Submonoid.square_subsemiringClosure {T : Type*} [CommSemiring T] :
    (Submonoid.square T).subsemiringClosure = .closure {x : T | IsSquare x} := by
  simp [Submonoid.subsemiringClosure_eq_closure]


theorem IsSumSq.prod [CommSemiring R] {ι : Type*} {I : Finset ι} {x : ι → R}
    (hx : ∀ i ∈ I, IsSumSq <| x i) : IsSumSq (∏ i ∈ I, x i) := by
  simpa using prod_mem (S := Subsemiring.sumSq R) (by simpa)

set_option linter.style.whitespace false in -- manual alignment is not recognised

