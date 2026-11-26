import KellnerBernoulli.Counting

/-!
# Digit sums
-/

namespace KellnerBernoulli

theorem digitSum_add_mul {b d m : ℕ} (hb : 2 ≤ b) (hd : d < b) :
    digitSum b (d + b * m) = d + digitSum b m := by
  rcases Nat.eq_zero_or_pos d with rfl | hd0
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [digitSum]
    · unfold digitSum
      rw [Nat.digits_add b (by omega) 0 m (by omega) (Or.inr hm.ne')]
      simp
  · unfold digitSum
    rw [Nat.digits_add b (by omega) d m hd (Or.inl hd0.ne')]
    simp

theorem digitSum_eq {b : ℕ} (hb : 2 ≤ b) (n : ℕ) :
    digitSum b n = n % b + digitSum b (n / b) := by
  conv_lhs => rw [← Nat.mod_add_div n b]
  exact digitSum_add_mul hb (Nat.mod_lt n (by omega))

@[simp] theorem digitSum_zero (b : ℕ) : digitSum b 0 = 0 := by simp [digitSum]

theorem digitSum_of_lt {b n : ℕ} (hb : 2 ≤ b) (h : n < b) : digitSum b n = n := by
  rw [digitSum_eq hb, Nat.mod_eq_of_lt h, Nat.div_eq_of_lt h, digitSum_zero, Nat.add_zero]

theorem digitSum_pos {b : ℕ} (hb : 2 ≤ b) : ∀ n, 0 < n → 0 < digitSum b n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rw [digitSum_eq hb]
    rcases Nat.eq_zero_or_pos (n % b) with h0 | h0
    · have hdiv : 0 < n / b := by
        have := Nat.mod_add_div n b
        rcases Nat.eq_zero_or_pos (n / b) with h1 | h1
        · rw [h0, h1] at this; omega
        · exact h1
      have := ih (n / b) (Nat.div_lt_self hn (by omega)) hdiv
      omega
    · omega

/-- Splitting the digits: for `t ≤ s_b(N)` there is `j ≤ N` with `s_b(j) = t` and no borrows. -/
theorem exists_split {b : ℕ} (hb : 2 ≤ b) : ∀ N t, t ≤ digitSum b N →
    ∃ j ≤ N, digitSum b j = t ∧ digitSum b (N - j) = digitSum b N - t := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro t ht
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp only [digitSum_zero, Nat.le_zero] at ht
      exact ⟨0, le_rfl, by simp [ht], by simp⟩
    · have hN' := digitSum_eq hb N
      set d := N % b with hd
      set M := N / b with hM
      have hdb : d < b := Nat.mod_lt N (by omega)
      have hNdm : N = d + b * M := (Nat.mod_add_div N b).symm
      by_cases htd : t ≤ d
      · refine ⟨t, by omega, digitSum_of_lt hb (by omega), ?_⟩
        have : N - t = (d - t) + b * M := by omega
        rw [this, digitSum_add_mul hb (by omega), hN']
        omega
      · obtain ⟨j', hj'1, hj'2, hj'3⟩ := ih M (Nat.div_lt_self hN (by omega)) (t - d) (by omega)
        refine ⟨d + b * j', ?_, ?_, ?_⟩
        · rw [hNdm]; nlinarith
        · rw [digitSum_add_mul hb hdb, hj'2]; omega
        · have : N - (d + b * j') = 0 + b * (M - j') := by
            rw [hNdm, Nat.mul_sub]; omega
          rw [this, digitSum_add_mul hb (by omega), hj'3, hN']
          have := digitSum_pos hb
          omega

theorem digitSum_succ {b n : ℕ} (hb : 2 ≤ b) (h : ¬ b ∣ n + 1) :
    digitSum b (n + 1) = digitSum b n + 1 := by
  have hmod : n % b + 1 < b := by
    by_contra hcon
    have h1 : n % b = b - 1 := by have := Nat.mod_lt n (show 0 < b by omega); omega
    apply h
    have := Nat.mod_add_div n b
    exact ⟨n / b + 1, by rw [Nat.mul_add, Nat.mul_one]; omega⟩
  have e1 : n + 1 = (n % b + 1) + b * (n / b) := by have := Nat.mod_add_div n b; omega
  rw [e1, digitSum_add_mul hb hmod, digitSum_eq hb n]
  omega

/-- `s_p(j) ≡ j (mod p - 1)`, in the form needed here. -/
theorem sub_one_dvd_digitSum_iff {p j : ℕ} (hp : 2 ≤ p) :
    (p - 1) ∣ digitSum p j ↔ (p - 1) ∣ j := by
  rcases Nat.eq_or_lt_of_le hp with rfl | hp3
  · simp
  · have h : p % (p - 1) = 1 := by
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 3 := ⟨p - 3, by omega⟩
      rw [show q + 3 - 1 = q + 2 by omega, show q + 3 = 1 + (q + 2) * 1 by ring,
        Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt (by omega)
    have hmod := Nat.modEq_digits_sum (p - 1) p h j
    rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero]
    unfold Nat.ModEq at hmod
    unfold digitSum
    rw [hmod]

/-- Kummer's theorem, the two directions needed here. -/
theorem digitSum_le_of_not_dvd_choose {p N j : ℕ} (hp : p.Prime) (hj : j ≤ N)
    (h : ¬ p ∣ N.choose j) : digitSum p j + digitSum p (N - j) ≤ digitSum p N := by
  have := Fact.mk hp
  have hk := sub_one_mul_multiplicity_choose_eq_sub_sum_digits (p := p) hj
  rw [multiplicity_eq_zero_of_not_dvd h, Nat.mul_zero] at hk
  unfold digitSum
  omega

theorem not_dvd_choose_of_digitSum {p N j : ℕ} (hp : p.Prime) (hj : j ≤ N)
    (h : digitSum p j + digitSum p (N - j) = digitSum p N) : ¬ p ∣ N.choose j := by
  have := Fact.mk hp
  have hk := sub_one_mul_multiplicity_choose_eq_sub_sum_digits (p := p) hj
  unfold digitSum at h
  rw [h, Nat.sub_self] at hk
  have hp1 : p - 1 ≠ 0 := by have := hp.two_le; omega
  have hm : multiplicity p (N.choose j) = 0 := by
    rcases Nat.mul_eq_zero.mp hk with h1 | h1
    · exact absurd h1 hp1
    · exact h1
  have hfin : FiniteMultiplicity p (N.choose j) :=
    Nat.finiteMultiplicity_iff.mpr ⟨hp.one_lt.ne', Nat.choose_pos hj⟩
  exact (multiplicity_eq_zero hfin).mp hm

end KellnerBernoulli
