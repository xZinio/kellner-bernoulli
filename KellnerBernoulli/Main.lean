import KellnerBernoulli.FiniteWindow
import KellnerBernoulli.Large
import KellnerBernoulli.SmallCases

/-!
# The main theorem

**Theorem** (conjectured by Kellner, 2017). For every `n > 192` there is a prime `p > √n` such that
the sum of the base-`p` digits of `n` is at least `p`.

The proof uses `ThetaBound` (Rosser and Schoenfeld 1975) only for `n ≥ (4 * 10 ^ 6) ^ 2`; below
that bound everything is unconditional.
-/

namespace KellnerBernoulli

theorem mem_goodPrimes_iff_digits {n p : ℕ} :
    p ∈ goodPrimes n ↔ p.Prime ∧ n < p ^ 2 ∧ p ≤ (Nat.digits p n).sum := by
  rw [mem_goodPrimes, pow_two]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    have := digitSum_of_lt_sq h1.two_le (by rw [pow_two]; exact h2)
    unfold digitSum at this
    rw [this]; exact h3
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    have := digitSum_of_lt_sq h1.two_le (by rw [pow_two]; exact h2)
    unfold digitSum at this
    rw [← this]; exact h3

/-- Many primes in `(s, s + U]` give three good primes. -/
theorem three_good_of_finset {n : ℕ} (hn : 1 ≤ n) {U : ℕ} (hU : 1 ≤ U) (T : Finset ℕ)
    (hT : ∀ p ∈ T, p.Prime ∧ Nat.sqrt n < p ∧ p ≤ Nat.sqrt n + U)
    (h : 2 * U ^ 2 + 8 * (Nat.sqrt n + U) < T.card * (Nat.sqrt n + U)) :
    3 ≤ (goodPrimes n).card := by
  classical
  set s := Nat.sqrt n with hs
  have hs1 : s * s ≤ n := Nat.sqrt_le n
  have hs2 : n < (s + 1) * (s + 1) := Nat.lt_succ_sqrt n
  have hspos : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with h0 | h0
    · rw [h0] at hs2; omega
    · exact h0
  set B := (Finset.Ioc s (s + U)).filter (fun m => Bad n m) with hB
  have hBc := card_bad_mul_le hs1 hs2 hspos hU
  rw [← hB] at hBc
  have hsub : T \ B ⊆ goodPrimes n := by
    intro p hp
    rw [Finset.mem_sdiff] at hp
    obtain ⟨h1, h2, h3⟩ := hT p hp.1
    rw [mem_goodPrimes]
    refine ⟨h1, lt_of_lt_of_le hs2 (Nat.mul_le_mul h2 h2), ?_⟩
    by_contra hc
    apply hp.2
    rw [hB, Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨h2, h3⟩, by unfold Bad; omega⟩
  have h1 := Finset.le_card_sdiff B T
  have h2 := Finset.card_le_card hsub
  have hlt : B.card + 2 < T.card := by
    by_contra hc
    rw [not_lt] at hc
    have := Nat.mul_le_mul_right (s + U) hc
    nlinarith
  omega

/-- Unconditionally: every `n` with `2015 ≤ n < (4 * 10 ^ 6) ^ 2` has three good primes. -/
theorem three_good_of_lt_sq {n : ℕ} (h1 : 2015 ≤ n) (h2 : n < 4000000 * 4000000) :
    3 ≤ (goodPrimes n).card := by
  rcases Nat.lt_or_ge n 100000000 with h | h
  · exact three_good_of_lt h1 h
  · set s := Nat.sqrt n with hs
    have hs1 : s * s ≤ n := Nat.sqrt_le n
    have hs2 : n < (s + 1) * (s + 1) := Nat.lt_succ_sqrt n
    have hlo : 9973 ≤ s := by
      by_contra hc
      have : s + 1 ≤ 9973 := by omega
      nlinarith
    have hhi : s < 4000000 := by
      by_contra hc
      have : 4000000 ≤ s := by omega
      nlinarith
    obtain ⟨T, U, hU, hTc, hT, hUU⟩ := hasWindow hlo hhi
    refine three_good_of_finset (by omega) hU T hT ?_
    rw [hTc, ← hs]
    nlinarith

/-- With `ThetaBound`: every `n ≥ 2015` has three good primes. -/
theorem three_good (h : ThetaBound) {n : ℕ} (hn : 2015 ≤ n) : 3 ≤ (goodPrimes n).card := by
  rcases Nat.lt_or_ge n (4000000 * 4000000) with h' | h'
  · exact three_good_of_lt_sq hn h'
  · set s := Nat.sqrt n with hs
    have hs : 4000000 ≤ s := Nat.le_sqrt.mpr h'
    obtain ⟨U, hU, hc⟩ := exists_many_primes h hs
    refine three_good_of_finset (by omega) hU (primesIn s U) ?_ hc
    intro p hp
    simp only [primesIn, Finset.mem_filter, Finset.mem_Ioc] at hp
    exact ⟨hp.2, hp.1.1, hp.1.2⟩

theorem two_good (h : ThetaBound) {n : ℕ} (hn : 1080 < n) : 2 ≤ (goodPrimes n).card := by
  rcases Nat.lt_or_ge n 2015 with h' | h'
  · exact two_good_of_lt hn (by omega)
  · exact le_trans (by norm_num) (three_good h h')

theorem one_good (h : ThetaBound) {n : ℕ} (hn : 192 < n) : 1 ≤ (goodPrimes n).card := by
  rcases Nat.lt_or_ge n 2015 with h' | h'
  · exact one_good_of_lt hn (by omega)
  · exact le_trans (by norm_num) (three_good h h')

/-- **Kellner's conjecture** ([Kellner 2017, Conjecture 1], [Kellner 2024, Conjecture 2(i)]):
for every `n > 192` there is a prime `p > √n` whose base-`p` digit sum of `n` is at least `p`. -/
theorem kellner_conjecture (h : ThetaBound) {n : ℕ} (hn : 192 < n) :
    ∃ p, p.Prime ∧ n < p ^ 2 ∧ p ≤ (Nat.digits p n).sum := by
  obtain ⟨p, hp⟩ := Finset.card_pos.mp (one_good h hn)
  exact ⟨p, mem_goodPrimes_iff_digits.mp hp⟩

/-- The same statement, unconditionally, for `n < 1.6 * 10 ^ 13`. -/
theorem kellner_conjecture_of_lt {n : ℕ} (hn : 192 < n) (hn' : n < 16 * 10 ^ 12) :
    ∃ p, p.Prime ∧ n < p ^ 2 ∧ p ≤ (Nat.digits p n).sum := by
  have : 1 ≤ (goodPrimes n).card := by
    rcases Nat.lt_or_ge n 2015 with h' | h'
    · exact one_good_of_lt hn (by omega)
    · exact le_trans (by norm_num) (three_good_of_lt_sq h' (by norm_num at hn' ⊢; omega))
  obtain ⟨p, hp⟩ := Finset.card_pos.mp this
  exact ⟨p, mem_goodPrimes_iff_digits.mp hp⟩

/-- The exceptions: for `n ≥ 1` there is no such prime exactly for these `26` values of `n`. -/
theorem kellner_exceptions (h : ThetaBound) {n : ℕ} (hn : 1 ≤ n) :
    (¬ ∃ p, p.Prime ∧ n < p ^ 2 ∧ p ≤ (Nat.digits p n).sum) ↔
      n ∈ ({1, 2, 4, 6, 10, 11, 12, 15, 16, 28, 29, 30, 35, 36, 58, 59, 60, 69, 70, 78, 79, 80, 174,
        190, 191, 192} : Finset ℕ) := by
  have hiff : (¬ ∃ p, p.Prime ∧ n < p ^ 2 ∧ p ≤ (Nat.digits p n).sum) ↔ goodPrimes n = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    simp only [mem_goodPrimes_iff_digits, not_exists]
  rw [hiff]
  rcases Nat.lt_or_ge 192 n with h1 | h1
  · constructor
    · intro he
      have := one_good h h1
      rw [he] at this
      simp at this
    · intro hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      omega
  · rw [goodPrimes_eq_empty_iff hn h1]
    simp [exceptions]

end KellnerBernoulli
