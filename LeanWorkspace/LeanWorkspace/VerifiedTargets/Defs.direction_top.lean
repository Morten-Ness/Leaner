import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P) in

theorem direction_top : (⊤ : AffineSubspace k P).direction = ⊤ := by
  obtain ⟨p⟩ := S.nonempty
  ext v
  refine ⟨imp_intro Submodule.mem_top, fun _hv => ?_⟩
  have hpv : ((v +ᵥ p) -ᵥ p : V) ∈ (⊤ : AffineSubspace k P).direction :=
    AffineSubspace.vsub_mem_direction (AffineSubspace.mem_top k V _) (AffineSubspace.mem_top k V _)
  rwa [vadd_vsub] at hpv

