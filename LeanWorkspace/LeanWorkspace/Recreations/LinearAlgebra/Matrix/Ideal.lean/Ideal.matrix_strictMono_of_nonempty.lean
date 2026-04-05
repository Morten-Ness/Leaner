import Mathlib

variable {R : Type*} [Semiring R]
         (n : Type*) [Fintype n] [DecidableEq n]

theorem matrix_strictMono_of_nonempty [Nonempty n] :
    StrictMono (Ideal.matrix (R := R) n) :=
  Ideal.matrix_monotone n |>.strictMono_of_injective <| fun I J eq => by
    ext x
    have : (∀ _ _, x ∈ I) ↔ (∀ _ _, x ∈ J) := congr((Matrix.of fun _ _ => x) ∈ $eq)
    simpa only [forall_const] using this

