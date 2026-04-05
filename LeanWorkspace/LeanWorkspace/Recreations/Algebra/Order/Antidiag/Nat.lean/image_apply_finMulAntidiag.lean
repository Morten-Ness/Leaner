import Mathlib

open scoped ArithmeticFunction

theorem image_apply_finMulAntidiag {d n : ℕ} {i : Fin d} (hd : d ≠ 1) :
    (Nat.finMulAntidiag d n).image (fun f => f i) = divisors n := by
  ext k
  simp only [mem_image, ne_eq, mem_divisors]
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨Nat.dvd_of_mem_finMulAntidiag hf _, (Nat.mem_finMulAntidiag.mp hf).2⟩
  · simp_rw [Nat.mem_finMulAntidiag]
    rintro ⟨⟨r, rfl⟩, hn⟩
    have hs : Nontrivial (Fin d) := by
      rw [Fin.nontrivial_iff_two_le]
      obtain rfl | hd' := eq_or_ne d 0
      · exact i.elim0
      lia
    obtain ⟨i', hi_ne⟩ := exists_ne i
    use fun j => if j = i then k else if j = i' then r else 1
    simp only [ite_true, and_true]
    rw [← Finset.mul_prod_erase (h := Finset.mem_univ i),
      ← Finset.mul_prod_erase (a := i')]
    · simp_all
    exact mem_erase.mpr ⟨hi_ne, Finset.mem_univ _⟩

