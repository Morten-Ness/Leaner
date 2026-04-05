import Mathlib

variable {α β n R : Type*}

theorem Fin.circulant_isSymm_iff : ∀ {n} {v : Fin n → α}, (Matrix.circulant v).IsSymm ↔ ∀ i, v (-i) = v i
  | 0 => by simp [IsSymm.ext_iff, IsEmpty.forall_iff]
  | _ + 1 => Matrix.circulant_isSymm_iff
