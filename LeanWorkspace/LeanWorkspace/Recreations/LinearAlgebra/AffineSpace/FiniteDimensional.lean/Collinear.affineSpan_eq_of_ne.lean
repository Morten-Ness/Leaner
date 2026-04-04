import Mathlib

variable (k : Type*) {V : Type*} {P : Type*}

variable {ι : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable {k}

variable (k)

variable (k P)

variable {P}

variable (k) in

theorem Collinear.affineSpan_eq_of_ne {s : Set P} (h : Collinear k s) {p₁ p₂ : P} (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) (hp₁p₂ : p₁ ≠ p₂) : line[k, p₁, p₂] = affineSpan k s := le_antisymm (affineSpan_mono _ (Set.insert_subset_iff.2 ⟨hp₁, Set.singleton_subset_iff.2 hp₂⟩))
    (affineSpan_le.2 fun _ hp => h.mem_affineSpan_of_mem_of_ne hp₁ hp₂ hp hp₁p₂)

