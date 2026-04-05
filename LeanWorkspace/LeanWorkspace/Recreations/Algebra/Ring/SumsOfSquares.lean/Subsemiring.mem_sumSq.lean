import Mathlib

variable {R : Type*}

variable {T : Type*} [CommSemiring T]

private theorem Submonoid.square_subsemiringClosure {T : Type*} [CommSemiring T] :
    (Submonoid.square T).subsemiringClosure = .closure {x : T | IsSquare x} := by
  simp [Submonoid.subsemiringClosure_eq_closure]


theorem mem_sumSq {s : T} : s ∈ Subsemiring.sumSq T ↔ IsSumSq s := by
  simp [← Subsemiring.mem_toNonUnitalSubsemiring]

