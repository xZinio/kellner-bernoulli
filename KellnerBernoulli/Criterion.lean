import KellnerBernoulli.Digits

/-!
# Denominators of Bernoulli polynomials and their derivatives (Proposition 9 of the paper)

From the theorem of von Staudt and Clausen (in Mathlib) and Kummer's theorem:
* a prime `p` divides the denominator of `B_n(x) - B_n` iff `s_p(n) ≥ p`;
* for `1 ≤ k ≤ n`, the `k`-th derivative of `B_n(x)` has integral coefficients iff every prime `p`
  divides `n (n - 1) ⋯ (n - k + 1)` or satisfies `s_p(n - k + 1) < p`.
-/

namespace KellnerBernoulli

/-- The indices `j` for which `p` divides the denominator of `B_j`. -/
def Jset (p j : ℕ) : Prop := (j = 1 ∧ p = 2) ∨ (0 < j ∧ Even j ∧ (p - 1) ∣ j)

theorem dvd_den_natCast_mul {p : ℕ} (hp : p.Prime) {q : ℚ} (h1 : p ∣ q.den)
    (h2 : ¬ p ^ 2 ∣ q.den) (h3 : ¬ (p : ℤ) ∣ q.num) (A : ℕ) :
    p ∣ ((A : ℚ) * q).den ↔ ¬ p ∣ A := by
  rw [Rat.mul_den]
  simp only [Rat.num_natCast, Rat.den_natCast, one_mul]
  set g := Nat.gcd ((A : ℤ) * q.num).natAbs q.den with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right _ q.den_pos
  obtain ⟨e, he⟩ : g ∣ q.den := Nat.gcd_dvd_right _ _
  have hdiv : q.den / g = e := by rw [he]; exact Nat.mul_div_cancel_left e hgpos
  rw [hdiv]
  constructor
  · intro hpe hpA
    have hpg : p ∣ g := by
      apply Nat.dvd_gcd
      · rw [Int.natAbs_mul]
        exact Dvd.dvd.mul_right (by simpa using hpA) _
      · exact h1
    apply h2
    rw [he, pow_two]
    exact Nat.mul_dvd_mul hpg hpe
  · intro hpA
    have hpg : ¬ p ∣ g := by
      intro hpg
      have h4 : p ∣ ((A : ℤ) * q.num).natAbs := hpg.trans (Nat.gcd_dvd_left _ _)
      rw [Int.natAbs_mul] at h4
      rcases (Nat.Prime.dvd_mul hp).mp h4 with h | h
      · exact hpA (by simpa using h)
      · exact h3 (Int.natCast_dvd.mpr h)
    rw [he] at h1
    rcases (Nat.Prime.dvd_mul hp).mp h1 with h | h
    · exact absurd h hpg
    · exact h

theorem bernoulli_den_of_Jset {p j : ℕ} (hp : p.Prime) (hJ : Jset p j) :
    p ∣ (bernoulli j).den ∧ ¬ p ^ 2 ∣ (bernoulli j).den ∧ ¬ (p : ℤ) ∣ (bernoulli j).num := by
  rcases hJ with ⟨rfl, rfl⟩ | ⟨hj, hev, hdvd⟩
  · rw [bernoulli_one]
    have hd : ((-1 / 2 : ℚ)).den = 2 := by norm_num
    have hn : ((-1 / 2 : ℚ)).num = -1 := by norm_num
    rw [hd, hn]
    decide
  · obtain ⟨k, rfl⟩ : ∃ k, j = 2 * k := ⟨j / 2, by obtain ⟨r, hr⟩ := hev; omega⟩
    have := Fact.mk hp
    exact ⟨Bernoulli.dvd_den_bernoulli (by omega) hdvd, Bernoulli.not_sq_dvd_den_bernoulli (by omega)
      hdvd, Bernoulli.not_dvd_num_bernoulli (by omega) hdvd⟩

theorem not_dvd_bernoulli_den {p j : ℕ} (hp : p.Prime) (hJ : ¬ Jset p j) :
    ¬ p ∣ (bernoulli j).den := by
  unfold Jset at hJ
  rcases Nat.even_or_odd j with hev | hodd
  · rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [hp.ne_one]
    · obtain ⟨k, rfl⟩ : ∃ k, j = 2 * k := ⟨j / 2, by obtain ⟨r, hr⟩ := hev; omega⟩
      have hpk : ¬ (p - 1) ∣ 2 * k := fun h => hJ (Or.inr ⟨hj, hev, h⟩)
      obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen k
      set S := (Finset.range (2 * k + 2)).filter (fun q => q.Prime ∧ (q - 1) ∣ 2 * k) with hS
      have hB : bernoulli (2 * k) = (z : ℚ) - ∑ q ∈ S, (1 : ℚ) / q := by rw [hz]; ring
      intro hden
      rw [hB] at hden
      have h1 := Rat.sub_den_dvd (z : ℚ) (∑ q ∈ S, (1 : ℚ) / q)
      rw [Rat.den_intCast, one_mul] at h1
      have h2 := (hden.trans h1).trans (Finset.Rat.den_sum_dvd_prod_den S (fun q => (1 : ℚ) / q))
      rcases (Prime.dvd_finsetProd_iff hp.prime _).mp h2 with ⟨q, hqS, hq⟩
      rw [hS, Finset.mem_filter] at hqS
      have hq' : ((1 : ℚ) / q).den = q := by
        rw [one_div, Rat.inv_natCast_den, if_neg hqS.2.1.ne_zero]
      rw [hq'] at hq
      have hpq : p = q := (Nat.prime_dvd_prime_iff_eq hp hqS.2.1).mp hq
      exact hpk (hpq ▸ hqS.2.2)
  · rcases Nat.eq_or_lt_of_le hodd.pos with h1 | h1
    · subst h1
      rw [bernoulli_one]
      have hd : ((-1 / 2 : ℚ)).den = 2 := by norm_num
      rw [hd]
      intro h
      have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h
      exact hJ (Or.inl ⟨rfl, this⟩)
    · rw [bernoulli_eq_zero_of_odd hodd h1]
      simp [hp.ne_one]

/-- A prime `p` divides the denominator of `A B_j` iff `p ∣ den B_j` and `p ∤ A`. -/
theorem dvd_den_mul_bernoulli_iff {p : ℕ} (hp : p.Prime) (A j : ℕ) :
    p ∣ ((A : ℚ) * bernoulli j).den ↔ Jset p j ∧ ¬ p ∣ A := by
  by_cases hJ : Jset p j
  · obtain ⟨h1, h2, h3⟩ := bernoulli_den_of_Jset hp hJ
    rw [dvd_den_natCast_mul hp h1 h2 h3]
    exact ⟨fun h => ⟨hJ, h⟩, fun h => h.2⟩
  · refine ⟨fun h => ?_, fun h => absurd h.1 hJ⟩
    have h1 := h.trans (Rat.mul_den_dvd (A : ℚ) (bernoulli j))
    rw [Rat.den_natCast, one_mul] at h1
    exact absurd h1 (not_dvd_bernoulli_den hp hJ)

/-! ## Digit conditions -/

theorem le_digitSum_of_Jset {p j : ℕ} (hp : p.Prime) (hJ : Jset p j) : p - 1 ≤ digitSum p j := by
  rcases hJ with ⟨rfl, rfl⟩ | ⟨hj, _, hdvd⟩
  · decide
  · have hpos := digitSum_pos hp.two_le j hj
    have hd := (sub_one_dvd_digitSum_iff hp.two_le).mpr hdvd
    exact Nat.le_of_dvd hpos hd

theorem Jset_of_digitSum {p j : ℕ} (hp : p.Prime) (h : digitSum p j = p - 1) : Jset p j := by
  have hp2 := hp.two_le
  have hj : 0 < j := by
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp at h; omega
    · exact hj
  have hdvd : (p - 1) ∣ j := (sub_one_dvd_digitSum_iff hp2).mp (by rw [h])
  rcases Nat.eq_or_lt_of_le hp2 with hp2' | hp3
  · -- `p = 2`: `j` is `1` or even
    subst hp2'
    rcases Nat.even_or_odd j with hev | hodd
    · exact Or.inr ⟨hj, hev, hdvd⟩
    · left
      refine ⟨?_, rfl⟩
      have e := digitSum_eq (b := 2) (by norm_num) j
      have h1 : j % 2 = 1 := Nat.odd_iff.mp hodd
      rw [h, h1] at e
      have h2 : digitSum 2 (j / 2) = 0 := by omega
      have h3 : j / 2 = 0 := by
        by_contra hcon
        have := digitSum_pos (b := 2) (by norm_num) (j / 2) (by omega)
        omega
      omega
  · right
    refine ⟨hj, ?_, hdvd⟩
    have : Even (p - 1) := by
      rcases hp.eq_two_or_odd' with h2 | hodd
      · omega
      · obtain ⟨r, hr⟩ := hodd
        exact ⟨r, by omega⟩
    exact this.two_dvd.trans hdvd |> even_iff_two_dvd.mpr

/-- (a) of Proposition 9: some `j ≤ N` with `p ∣ den B_j` and `p ∤ D C(N, j)`. -/
theorem exists_Jset_iff {p : ℕ} (hp : p.Prime) (N D : ℕ) :
    (∃ j ≤ N, Jset p j ∧ ¬ p ∣ D * N.choose j) ↔ ¬ p ∣ D ∧ p - 1 ≤ digitSum p N := by
  constructor
  · rintro ⟨j, hjN, hJ, hdiv⟩
    have hD : ¬ p ∣ D := fun h => hdiv (Dvd.dvd.mul_right h _)
    have hC : ¬ p ∣ N.choose j := fun h => hdiv (Dvd.dvd.mul_left h _)
    have h1 := le_digitSum_of_Jset hp hJ
    have h2 := digitSum_le_of_not_dvd_choose hp hjN hC
    exact ⟨hD, by omega⟩
  · rintro ⟨hD, hN⟩
    obtain ⟨j, hjN, hj1, hj2⟩ := exists_split hp.two_le N (p - 1) hN
    refine ⟨j, hjN, Jset_of_digitSum hp hj1, ?_⟩
    have hC := not_dvd_choose_of_digitSum hp hjN (by omega)
    intro h
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · exact hD h
    · exact hC h

/-- (b) of Proposition 9: some `j < n` with `p ∣ den B_j` and `p ∤ C(n, j)`. -/
theorem exists_Jset_lt_iff {p : ℕ} (hp : p.Prime) (n : ℕ) :
    (∃ j < n, Jset p j ∧ ¬ p ∣ n.choose j) ↔ p ≤ digitSum p n := by
  constructor
  · rintro ⟨j, hjn, hJ, hC⟩
    have h1 := le_digitSum_of_Jset hp hJ
    have h2 := digitSum_le_of_not_dvd_choose hp hjn.le hC
    have h3 := digitSum_pos hp.two_le (n - j) (by omega)
    have := hp.two_le
    omega
  · intro hn
    have hp2 := hp.two_le
    obtain ⟨j, hjN, hj1, hj2⟩ := exists_split hp2 n (p - 1) (by omega)
    have hjn : j < n := by
      rcases Nat.lt_or_ge j n with h | h
      · exact h
      · have : n - j = 0 := by omega
        rw [this, digitSum_zero] at hj2
        omega
    exact ⟨j, hjn, Jset_of_digitSum hp hj1, not_dvd_choose_of_digitSum hp hjN (by omega)⟩

/-! ## Coefficients -/

/-- All coefficients of a polynomial over `ℚ` are integers. -/
def IntCoeffs (P : Polynomial ℚ) : Prop := ∀ i, (P.coeff i).den = 1

theorem intCoeffs_iff_mem_lifts (P : Polynomial ℚ) :
    IntCoeffs P ↔ P ∈ Polynomial.lifts (Int.castRingHom ℚ) := by
  rw [Polynomial.lifts_iff_coeff_lifts]
  refine forall_congr' fun i => ?_
  rw [Rat.den_eq_one_iff]
  constructor
  · intro h; exact ⟨_, h⟩
  · rintro ⟨z, hz⟩
    rw [← hz]
    simp

theorem descFactorial_mul_choose (n k m : ℕ) (h : m + k ≤ n) :
    (m + k).descFactorial k * n.choose (m + k) = n.descFactorial k * (n - k).choose m := by
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose,
    mul_assoc, mul_assoc, mul_comm ((m + k).choose k), Nat.choose_mul (n := n) (by omega : k ≤ m + k)]
  simp

theorem coeff_iterate_derivative_bernoulli (n k m : ℕ) :
    (Polynomial.derivative^[k] (Polynomial.bernoulli n)).coeff m =
      if m + k ≤ n then ((n.descFactorial k * (n - k).choose m : ℕ) : ℚ) * bernoulli (n - k - m)
      else 0 := by
  rw [Polynomial.coeff_iterate_derivative, Polynomial.coeff_bernoulli]
  split_ifs with h
  · rw [nsmul_eq_mul, ← descFactorial_mul_choose n k m h]
    push_cast
    rw [show n - (m + k) = n - k - m by omega]
    ring
  · simp

theorem den_eq_one_iff_forall_prime (q : ℚ) : q.den = 1 ↔ ∀ p, p.Prime → ¬ p ∣ q.den := by
  constructor
  · intro h p hp hdvd
    rw [h] at hdvd
    exact hp.one_lt.ne' (Nat.dvd_one.mp hdvd)
  · intro h
    by_contra hne
    exact h _ (Nat.minFac_prime hne) (Nat.minFac_dvd _)

/-- Proposition 9 for derivatives. -/
theorem intCoeffs_iterate_derivative_iff (n k : ℕ) (hk : k ≤ n) :
    IntCoeffs (Polynomial.derivative^[k] (Polynomial.bernoulli n)) ↔
      ∀ p, p.Prime → p ∣ n.descFactorial k ∨ digitSum p (n - k) < p - 1 := by
  constructor
  · intro h p hp
    by_contra hcon
    rw [not_or, not_lt] at hcon
    obtain ⟨j, hj, hJ, hdiv⟩ := (exists_Jset_iff hp (n - k) (n.descFactorial k)).mpr hcon
    have hc := h (n - k - j)
    rw [coeff_iterate_derivative_bernoulli, if_pos (by omega),
      show n - k - (n - k - j) = j by omega, Nat.choose_symm (by omega)] at hc
    exact (den_eq_one_iff_forall_prime _).mp hc p hp
      ((dvd_den_mul_bernoulli_iff hp _ _).mpr ⟨hJ, hdiv⟩)
  · intro h m
    rw [coeff_iterate_derivative_bernoulli]
    split_ifs with hm
    · rw [den_eq_one_iff_forall_prime]
      intro p hp hdvd
      rw [dvd_den_mul_bernoulli_iff hp] at hdvd
      have hex : ∃ j ≤ n - k, Jset p j ∧ ¬ p ∣ n.descFactorial k * (n - k).choose j :=
        ⟨n - k - m, by omega, hdvd.1, by rw [Nat.choose_symm (show m ≤ n - k by omega)]; exact hdvd.2⟩
      rw [exists_Jset_iff hp] at hex
      rcases h p hp with h1 | h1
      · exact hex.1 h1
      · omega
    · simp

/-- The same with the condition of the paper: `p ∣ (n)_k` or `s_p(n - k + 1) < p`. -/
theorem intCoeffs_iterate_derivative_iff' (n k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ n) :
    IntCoeffs (Polynomial.derivative^[k] (Polynomial.bernoulli n)) ↔
      ∀ p, p.Prime → p ∣ n.descFactorial k ∨ digitSum p (n - k + 1) < p := by
  rw [intCoeffs_iterate_derivative_iff n k hk]
  refine forall_congr' fun p => forall_congr' fun hp => ?_
  have hfac : (n - k + 1) ∣ n.descFactorial k := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [Nat.descFactorial_succ]
    exact ⟨_, by rw [show n - k' = n - (k' + 1) + 1 by omega]⟩
  by_cases hD : p ∣ n.descFactorial k
  · simp [hD]
  · have hm : ¬ p ∣ n - k + 1 := fun h => hD (h.trans hfac)
    rw [digitSum_succ hp.two_le hm]
    have := hp.two_le
    simp only [hD, false_or]
    omega

theorem intCoeffs_iterate_derivative_of_lt (n k : ℕ) (h : n < k) :
    IntCoeffs (Polynomial.derivative^[k] (Polynomial.bernoulli n)) := by
  intro m
  rw [coeff_iterate_derivative_bernoulli, if_neg (by omega)]
  rfl

end KellnerBernoulli
