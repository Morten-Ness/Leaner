import Mathlib

variable (k : Type*) {V : Type*} {P : Type*}

variable {ι : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable {k}

variable (k)

variable (k P)

variable {P}

variable (k) in

theorem Collinear.mem_affineSpan_of_mem_of_ne {s : Set P} (h : Collinear k s) {p₁ p₂ p₃ : P}
    (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) (hp₃ : p₃ ∈ s) (hp₁p₂ : p₁ ≠ p₂) : p₃ ∈ line[k, p₁, p₂] := by
  rw [collinear_iff_of_mem hp₁] at h
  rcases h with ⟨v, h⟩
  rcases h p₂ hp₂ with ⟨r₂, rfl⟩
  rcases h p₃ hp₃ with ⟨r₃, rfl⟩
  rw [vadd_left_mem_affineSpan_pair]
  refine ⟨r₃ / r₂, ?_⟩
  have h₂ : r₂ ≠ 0 := by
    rintro rfl
    simp at hp₁p₂
  simp [smul_smul, h₂]

