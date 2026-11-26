import KellnerBernoulli.Main

/-!
# Consequences for Bernoulli polynomials

* `bernoulli_derivative_intCoeffs_iff`: for `n ≥ 1`, `B_n'(x) ∈ ℤ[x]` iff
  `n ∈ {1, 2, 4, 6, 10, 12, 28, 30, 36, 60}` ([Kellner 2024, Conjecture 1(ii)], OEIS A094960);
* `bernoulli_iterate_derivative_two` / `_three`: the same for the second and third derivative
  ([Kellner 2024, Conjecture 15], OEIS A366169, A366186);
* `oeis_A195441`: `denom(B_n(x) - B_n) = rad(n + 1)` iff `n ∈ {3, 5, 8, 9, 11, 27, 29, 35, 59}`
  ([Kellner 2024, Conjecture 11], OEIS A195441), with the definition and conclusion of
  `OeisA195441.conjecture` in `formal-conjectures`, under the hypothesis `ThetaBound`
  (see also `bernoulli_sub_den_eq_radical_iff` in `Denominators.lean`);
* `kellner2017`: [Kellner 2017, Conjecture 1];
* `alekseyev`: Alekseyev's conjecture in OEIS A094960.
-/

namespace KellnerBernoulli

theorem not_dvd_of_mem_goodPrimes {m p : ℕ} (hp : p ∈ goodPrimes m) : ¬ p ∣ m := by
  rw [mem_goodPrimes] at hp
  obtain ⟨_, h2, h3⟩ := hp
  intro hd
  rw [Nat.mod_eq_zero_of_dvd hd, Nat.add_zero] at h3
  have : p * p ≤ m :=
    calc p * p ≤ m / p * p := Nat.mul_le_mul_right _ h3
      _ ≤ m := Nat.div_mul_le_self m p
  omega

theorem one_le_of_mem_goodPrimes {m p : ℕ} (hp : p ∈ goodPrimes m) : 1 ≤ m := by
  rw [mem_goodPrimes] at hp
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp at hp
  · exact hm

theorem sqrt_lt_of_mem_goodPrimes {m p : ℕ} (hp : p ∈ goodPrimes m) :
    1 ≤ Nat.sqrt m ∧ Nat.sqrt m + 1 ≤ p := by
  rw [mem_goodPrimes] at hp
  obtain ⟨h1, h2, h3⟩ := hp
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp at h3; exact absurd h3 h1.ne_zero
    · exact hm
  refine ⟨Nat.le_sqrt.mpr (by omega), ?_⟩
  by_contra hc
  have : p ≤ Nat.sqrt m := by omega
  have := Nat.mul_le_mul this this
  have := Nat.sqrt_le m
  omega

/-- Two different good primes for `m` do not both divide `m + j`, `j ≤ 2`. -/
theorem not_both_dvd {m p q j : ℕ} (hp : p ∈ goodPrimes m) (hq : q ∈ goodPrimes m) (hpq : p ≠ q)
    (hj : j ≤ 2) (h1 : p ∣ m + j) (h2 : q ∣ m + j) : False := by
  have hcop : Nat.Coprime p q :=
    (Nat.coprime_primes (mem_goodPrimes.mp hp).1 (mem_goodPrimes.mp hq).1).mpr hpq
  have hle : p * q ≤ m + j :=
    Nat.le_of_dvd (by have := one_le_of_mem_goodPrimes hp; omega)
      (Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h1 h2)
  obtain ⟨hs, hp1⟩ := sqrt_lt_of_mem_goodPrimes hp
  obtain ⟨_, hq1⟩ := sqrt_lt_of_mem_goodPrimes hq
  have hs2 : m < (Nat.sqrt m + 1) * (Nat.sqrt m + 1) := Nat.lt_succ_sqrt m
  set s := Nat.sqrt m
  rcases Nat.lt_or_gt_of_ne hpq with hlt | hlt
  · have : (s + 1) * (s + 2) ≤ p * q := Nat.mul_le_mul hp1 (by omega)
    nlinarith
  · have : (s + 2) * (s + 1) ≤ p * q := Nat.mul_le_mul (by omega) hq1
    nlinarith

theorem dvd_descFactorial {p m k : ℕ} (hp : p.Prime) (h : p ∣ (m + k - 1).descFactorial k) :
    ∃ j < k, p ∣ m + j := by
  rw [Nat.descFactorial_eq_prod_range] at h
  obtain ⟨i, hi, hd⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp h
  rw [Finset.mem_range] at hi
  exact ⟨k - 1 - i, by omega, by rwa [show m + (k - 1 - i) = m + k - 1 - i by omega]⟩

/-- Of three good primes for `m`, one does not divide `m (m + 1) ⋯ (m + k - 1)`, `k ≤ 3`. -/
theorem exists_good_not_dvd {m k : ℕ} (hk : k ≤ 3) (h3 : 3 ≤ (goodPrimes m).card) :
    ∃ p ∈ goodPrimes m, ¬ p ∣ (m + k - 1).descFactorial k := by
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp (show 2 < (goodPrimes m).card by omega)
  by_contra hcon
  push Not at hcon
  have key : ∀ x ∈ goodPrimes m, ∃ j, 1 ≤ j ∧ j ≤ 2 ∧ x ∣ m + j := by
    intro x hx
    obtain ⟨j, hj, hd⟩ := dvd_descFactorial (mem_goodPrimes.mp hx).1 (hcon x hx)
    refine ⟨j, ?_, by omega, hd⟩
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact absurd (by simpa using hd) (not_dvd_of_mem_goodPrimes hx)
    · exact hj0
  obtain ⟨ja, ha1, ha2, hda⟩ := key a ha
  obtain ⟨jb, hb1, hb2, hdb⟩ := key b hb
  obtain ⟨jc, hc1, hc2, hdc⟩ := key c hc
  rcases (show ja = jb ∨ ja = jc ∨ jb = jc by omega) with e | e | e
  · subst e; exact not_both_dvd ha hb hab ha2 hda hdb
  · subst e; exact not_both_dvd ha hc hac ha2 hda hdc
  · subst e; exact not_both_dvd hb hc hbc hb2 hdb hdc

/-! ## Derivatives -/

theorem iterate_derivative_aux (h : ThetaBound) (k : ℕ) (hk1 : 1 ≤ k) (hk3 : k ≤ 3) (S : List ℕ)
    (htab : derivTable k S 2016 = true) (hS : ∀ x ∈ S, x ≤ 2016)
    (hlow : ∀ n, 1 ≤ n → n < k → n ∈ S) (n : ℕ) (hn : 1 ≤ n) :
    IntCoeffs (Polynomial.derivative^[k] (Polynomial.bernoulli n)) ↔ n ∈ S := by
  rcases Nat.lt_or_ge n k with hnk | hnk
  · exact ⟨fun _ => hlow n hn hnk, fun _ => intCoeffs_iterate_derivative_of_lt n k hnk⟩
  rw [intCoeffs_iterate_derivative_iff' n k hk1 hnk]
  rcases Nat.lt_or_ge 2016 n with hbig | hsmall
  · obtain ⟨p, hp, hpd⟩ := exists_good_not_dvd (m := n - k + 1) hk3 (three_good h (by omega))
    rw [show n - k + 1 + k - 1 = n by omega] at hpd
    constructor
    · intro hall
      exfalso
      obtain ⟨hpp, hlt, hle⟩ := mem_goodPrimes.mp hp
      rcases hall p hpp with h1 | h1
      · exact hpd h1
      · rw [digitSum_of_lt_sq hpp.two_le (by rw [pow_two]; exact hlt)] at h1
        omega
    · intro hmem
      have := hS n hmem
      omega
  · have ht := List.all_eq_true.mp htab n (List.mem_range'.mpr ⟨n - k, by omega, by omega⟩)
    rw [beq_iff_eq, Bool.eq_iff_iff, critB_iff (by omega), List.contains_iff_mem] at ht
    exact ht

/-- **For `n ≥ 1`, `B_n'(x)` has integral coefficients iff `n ∈ {1, 2, 4, 6, 10, 12, 28, 30, 36, 60}`**
([Kellner 2024, Conjecture 1(ii)]). -/
theorem bernoulli_derivative_intCoeffs_iff (h : ThetaBound) {n : ℕ} (hn : 1 ≤ n) :
    IntCoeffs (Polynomial.derivative (Polynomial.bernoulli n)) ↔
      n ∈ ({1, 2, 4, 6, 10, 12, 28, 30, 36, 60} : Finset ℕ) := by
  have := iterate_derivative_aux h 1 le_rfl (by norm_num) S1 derivTable1 (by decide)
    (fun n h1 h2 => by omega) n hn
  rw [Function.iterate_one] at this
  rw [this]
  simp [S1]

/-- The same, with integrality expressed as lifting to `ℤ[X]`. -/
theorem bernoulli_derivative_mem_lifts_iff (h : ThetaBound) {n : ℕ} (hn : 1 ≤ n) :
    Polynomial.derivative (Polynomial.bernoulli n) ∈ Polynomial.lifts (Int.castRingHom ℚ) ↔
      n ∈ ({1, 2, 4, 6, 10, 12, 28, 30, 36, 60} : Finset ℕ) := by
  rw [← intCoeffs_iff_mem_lifts, bernoulli_derivative_intCoeffs_iff h hn]

/-- The second derivative ([Kellner 2024, Conjecture 15], OEIS A366169). -/
theorem bernoulli_iterate_derivative_two (h : ThetaBound) {n : ℕ} (hn : 1 ≤ n) :
    IntCoeffs (Polynomial.derivative^[2] (Polynomial.bernoulli n)) ↔ n ∈ S2 :=
  iterate_derivative_aux h 2 (by norm_num) (by norm_num) S2 derivTable2 (by decide)
    (fun n h1 h2 => by simp [S2]; omega) n hn

/-- The third derivative ([Kellner 2024, Conjecture 15], OEIS A366186). -/
theorem bernoulli_iterate_derivative_three (h : ThetaBound) {n : ℕ} (hn : 1 ≤ n) :
    IntCoeffs (Polynomial.derivative^[3] (Polynomial.bernoulli n)) ↔ n ∈ S3 :=
  iterate_derivative_aux h 3 (by norm_num) (by norm_num) S3 derivTable3 (by decide)
    (fun n h1 h2 => by simp [S3]; omega) n hn

/-! ## OEIS A195441 -/

/-- `a(n)`, the denominator of `B_{n+1}(x) - B_{n+1}` (OEIS A195441), defined exactly as in
`FormalConjectures/OEIS/195441.lean` of `google-deepmind/formal-conjectures`. -/
def a (n : ℕ) : ℕ :=
  let N := n + 1
  (Finset.Icc 1 N).lcm fun k => (((N.choose k : ℚ) * bernoulli (N - k)).den)

theorem a_ne_zero (n : ℕ) : a n ≠ 0 := by
  unfold a
  simp only
  rw [Ne, Finset.lcm_eq_zero_iff]
  push Not
  intro k _
  exact Rat.den_ne_zero _

theorem den_factorization_le_one (p A j : ℕ) :
    ((A : ℚ) * bernoulli j).den.factorization p ≤ 1 := by
  by_cases hp : p.Prime
  · by_contra hc
    rw [not_le] at hc
    have hsq : p ^ 2 ∣ ((A : ℚ) * bernoulli j).den :=
      (hp.pow_dvd_iff_le_factorization (Rat.den_ne_zero _)).mpr hc
    have hdvd : ((A : ℚ) * bernoulli j).den ∣ (bernoulli j).den := by
      have := Rat.mul_den_dvd (A : ℚ) (bernoulli j)
      rwa [Rat.den_natCast, one_mul] at this
    by_cases hJ : Jset p j
    · exact (bernoulli_den_of_Jset hp hJ).2.1 (hsq.trans hdvd)
    · exact not_dvd_bernoulli_den hp hJ ((dvd_pow_self p two_ne_zero).trans (hsq.trans hdvd))
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

theorem a_squarefree (n : ℕ) : Squarefree (a n) := by
  rw [Nat.squarefree_iff_factorization_le_one (a_ne_zero n)]
  intro p
  unfold a
  simp only
  rw [Finset.factorization_lcm (fun k _ => Rat.den_ne_zero _) p]
  exact Finset.sup_le fun k _ => den_factorization_le_one p _ _

/-- A prime `p` divides `a(n - 1)` iff `s_p(n) ≥ p`. -/
theorem prime_dvd_a_iff {n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime) :
    p ∣ a (n - 1) ↔ p ≤ digitSum p n := by
  rw [hp.dvd_iff_one_le_factorization (a_ne_zero _)]
  unfold a
  simp only [show n - 1 + 1 = n by omega]
  rw [Finset.factorization_lcm (fun k _ => Rat.den_ne_zero _) p,
    Finset.le_sup_iff (by norm_num), ← exists_Jset_lt_iff hp n]
  constructor
  · rintro ⟨k, hk, hle⟩
    rw [← hp.dvd_iff_one_le_factorization (Rat.den_ne_zero _), dvd_den_mul_bernoulli_iff hp] at hle
    rw [Finset.mem_Icc] at hk
    refine ⟨n - k, by omega, hle.1, ?_⟩
    rw [Nat.choose_symm hk.2]
    exact hle.2
  · rintro ⟨j, hj, hJ, hC⟩
    refine ⟨n - j, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    rw [← hp.dvd_iff_one_le_factorization (Rat.den_ne_zero _), dvd_den_mul_bernoulli_iff hp,
      show n - (n - j) = j by omega, Nat.choose_symm (by omega)]
    exact ⟨hJ, hC⟩

theorem prime_dvd_radical_iff {p m : ℕ} (hp : p.Prime) (hm : m ≠ 0) :
    p ∣ UniqueFactorizationMonoid.radical m ↔ p ∣ m :=
  UniqueFactorizationMonoid.dvd_radical_iff_of_irreducible hp.prime.irreducible hm

theorem a_eq_radical_iff {n : ℕ} (hn : 1 ≤ n) :
    a (n - 1) = UniqueFactorizationMonoid.radical (n + 1) ↔
      ∀ p, p.Prime → (p ≤ digitSum p n ↔ p ∣ n + 1) := by
  rw [Nat.Squarefree.ext_iff (a_squarefree _) UniqueFactorizationMonoid.squarefree_radical]
  refine forall_congr' fun p => forall_congr' fun hp => ?_
  rw [prime_dvd_a_iff hn hp, prime_dvd_radical_iff hp (by omega)]

theorem radical_check_iff {n : ℕ} (hn : n + 1 < 2030) :
    allR (fun p => Nat.blt (n + 1) p || (Nat.ble p (dsum p n) == Nat.beq ((n + 1) % p) 0))
        Data.trial = true ↔ ∀ p, p.Prime → (p ≤ digitSum p n ↔ p ∣ n + 1) := by
  rw [allR_eq_true]
  constructor
  · intro h p hp
    rcases Nat.lt_or_ge (n + 1) p with hlt | hle
    · rw [digitSum_of_lt hp.two_le (by omega)]
      constructor
      · intro h1; omega
      · intro h1; have := Nat.le_of_dvd (by omega) h1; omega
    · have h1 := h p (mem_trial hp (by omega))
      rw [Bool.or_eq_true, Nat.blt_eq, beq_iff_eq, Bool.eq_iff_iff, Nat.ble_eq, Nat.beq_eq] at h1
      rcases h1 with h1 | h1
      · omega
      · rw [dsum_eq hp.two_le (by omega), ← Nat.dvd_iff_mod_eq_zero] at h1
        exact h1
  · intro h p hmem
    have hp := prime_of_mem_trial hmem
    rw [Bool.or_eq_true, Nat.blt_eq, beq_iff_eq, Bool.eq_iff_iff, Nat.ble_eq, Nat.beq_eq]
    rcases Nat.lt_or_ge (n + 1) p with hlt | hle
    · left; exact hlt
    · right
      rw [dsum_eq hp.two_le (by omega), ← Nat.dvd_iff_mod_eq_zero]
      exact h p hp

/-- **OEIS A195441** ([Kellner 2024, Conjecture 11]).  The definition of `a` and the conclusion are those
of `OeisA195441.conjecture` in `google-deepmind/formal-conjectures`; unlike that statement, this theorem
assumes `ThetaBound`. -/
theorem oeis_A195441 (h : ThetaBound) :
    {n : ℕ | 1 ≤ n ∧ a (n - 1) = UniqueFactorizationMonoid.radical (n + 1)} =
      ({3, 5, 8, 9, 11, 27, 29, 35, 59} : Finset ℕ) := by
  ext n
  simp only [Set.mem_ofPred_eq, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [a_eq_radical_iff hn]
  rcases Nat.lt_or_ge 1080 n with hbig | hsmall
  · constructor
    · rintro ⟨_, hall⟩
      obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (two_good h hbig)
      have good_dvd : ∀ x ∈ goodPrimes n, x ∣ n + 1 := by
        intro x hx
        obtain ⟨hx1, hx2, hx3⟩ := mem_goodPrimes.mp hx
        refine (hall x hx1).mp ?_
        rw [digitSum_of_lt_sq hx1.two_le (by rw [pow_two]; exact hx2)]
        exact hx3
      exact (not_both_dvd (j := 1) hp hq hpq (by norm_num) (good_dvd p hp) (good_dvd q hq)).elim
    · intro hmem; omega
  · have ht := List.all_eq_true.mp radicalTable_true n
      (List.mem_range'.mpr ⟨n - 1, by omega, by omega⟩)
    rw [beq_iff_eq, Bool.eq_iff_iff, radical_check_iff (by omega), List.contains_iff_mem] at ht
    rw [ht]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega

/-! ## Two further conjectures -/

/-- [Kellner 2017, Conjecture 1]: for `n > 192` the largest prime `P` with `s_P(n) ≥ P` satisfies
`P > √n` and `(n + 1) / P < √n`.  Equivalently, some prime `p` with `s_p(n) ≥ p` satisfies both. -/
theorem kellner2017 (h : ThetaBound) {n : ℕ} (hn : 192 < n) :
    ∃ p, p.Prime ∧ p ≤ (Nat.digits p n).sum ∧ n < p ^ 2 ∧ (n + 1) ^ 2 < n * p ^ 2 := by
  rcases Nat.lt_or_ge 1080 n with hbig | hsmall
  · obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (two_good h hbig)
    -- take the larger of the two
    have main : ∀ x y, x ∈ goodPrimes n → y ∈ goodPrimes n → x < y →
        ∃ p, p.Prime ∧ p ≤ (Nat.digits p n).sum ∧ n < p ^ 2 ∧ (n + 1) ^ 2 < n * p ^ 2 := by
      intro x y hx hy hxy
      obtain ⟨hy1, hy2, hy3⟩ := mem_goodPrimes_iff_digits.mp hy
      refine ⟨y, hy1, hy3, hy2, ?_⟩
      obtain ⟨hs, hx1⟩ := sqrt_lt_of_mem_goodPrimes hx
      have hs2 : n < (Nat.sqrt n + 1) * (Nat.sqrt n + 1) := Nat.lt_succ_sqrt n
      have hs1 := Nat.sqrt_le n
      set s := Nat.sqrt n
      have hy4 : s + 2 ≤ y := by omega
      have : (s + 2) * (s + 2) ≤ y * y := Nat.mul_le_mul hy4 hy4
      have hn1 : 1 ≤ n := by omega
      nlinarith
    rcases Nat.lt_or_gt_of_ne hpq with hlt | hlt
    · exact main p q hp hq hlt
    · exact main q p hq hp hlt
  · have ht := List.all_eq_true.mp lambdaTable_true n
      (List.mem_range'.mpr ⟨n - 193, by omega, by omega⟩)
    obtain ⟨p, hmem, hp⟩ := List.any_eq_true.mp ht
    have hpp := prime_of_mem_trial hmem
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hp
    rw [dsum_eq hpp.two_le (by omega)] at hp
    refine ⟨p, hpp, hp.1, ?_, by rw [pow_two, pow_two]; exact hp.2⟩
    by_contra hc
    rw [not_lt] at hc
    have : n * (p * p) ≤ n * n := Nat.mul_le_mul_left _ (by rw [← pow_two]; exact hc)
    nlinarith [hp.2]

/-- Alekseyev's conjecture (OEIS A094960): for every `k > 78` there is a prime `p ≥ 3` such that
the last two base-`p` digits of `k` add up to at least `p`. -/
theorem alekseyev (h : ThetaBound) {k : ℕ} (hk : 78 < k) :
    ∃ p, p.Prime ∧ 3 ≤ p ∧ p ≤ k % p + (k / p) % p := by
  rcases Nat.lt_or_ge 192 k with hbig | hsmall
  · obtain ⟨p, hp⟩ := Finset.card_pos.mp (one_good h hbig)
    obtain ⟨h1, h2, h3⟩ := mem_goodPrimes.mp hp
    have hq : k / p < p := Nat.div_lt_of_lt_mul h2
    refine ⟨p, h1, ?_, by rw [Nat.mod_eq_of_lt hq]; omega⟩
    by_contra hc
    have : p ≤ 2 := by omega
    have := Nat.mul_le_mul this this
    omega
  · have ht := List.all_eq_true.mp alekseyevTable_true k
      (List.mem_range'.mpr ⟨k - 79, by omega, by omega⟩)
    obtain ⟨p, hmem, hp⟩ := List.any_eq_true.mp ht
    simp only [Bool.and_eq_true, Nat.ble_eq] at hp
    exact ⟨p, prime_of_mem_trial hmem, hp.1, hp.2⟩

end KellnerBernoulli
