FAIL
import Mathlib

variable {R k V1 P1 V2 P2 V3 P3 : Type*}

variable [Ring k] [AddCommGroup V1] [AddTorsor V1 P1] [AddCommGroup V2] [AddTorsor V2 P2]

variable [AddCommGroup V3] [AddTorsor V3 P3] [Module k V1] [Module k V2] [Module k V3]

variable {ι : Type*} {φv φp : ι → Type*} [(i : ι) → AddCommGroup (φv i)]
  [(i : ι) → Module k (φv i)] [(i : ι) → AddTorsor (φv i) (φp i)]

variable (fp : (i : ι) → (P1 →ᵃ[k] φp i)) (fv : (i : ι) → (P1 →ᵃ[k] φv i))
  (f' : ι → P1 →ᵃ[k] P2)

variable [Finite ι] [DecidableEq ι] {f g : ((i : ι) → φv i) →ᵃ[k] P2}

theorem pi_ext_nonempty [Nonempty ι] (h : ∀ i x, f (Pi.single i x) = g (Pi.single i x)) :
    f = g := by
  let i0 : ι := Classical.choice ‹Nonempty ι›
  have hz : f 0 = g 0 := by
    simpa using h i0 (0 : φv i0)
  have hlin : f.linear = g.linear := by
    ext i x
    have hfx : f (Pi.single i x) = f 0 +ᵥ f.linear (Pi.single i x) := by
      simpa using (f.map_vadd 0 (Pi.single i x))
    have hgx : g (Pi.single i x) = g 0 +ᵥ g.linear (Pi.single i x) := by
      simpa using (g.map_vadd 0 (Pi.single i x))
    rw [hfx, hgx, hz] at h
    have hs := h i x
    rw [hfx, hgx, hz] at hs
    exact Pi.single_left_injective k φv i (by
      simpa using vadd_left_cancel hs)
  ext x
  have hf0x : f x = f 0 +ᵥ f.linear x := by
    simpa using (f.map_vadd 0 x)
  have hg0x : g x = g 0 +ᵥ g.linear x := by
    simpa using (g.map_vadd 0 x)
  rw [hf0x, hg0x, hz, hlin]
