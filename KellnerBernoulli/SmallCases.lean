import KellnerBernoulli.Criterion
import KellnerBernoulli.FiniteChain

/-!
# Small cases

Kernel-checked tables for `n ≤ 2016`.  Every prime `p ≤ 2016` is in `Data.trial`.
-/

namespace KellnerBernoulli

/-- Base-`p` digit sum with fuel `f` (correct for `n < p ^ f`). -/
def dsumF (p : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, n => n % p + dsumF p f (n / p)

theorem dsumF_eq {p : ℕ} (hp : 2 ≤ p) : ∀ f n, n < p ^ f → dsumF p f n = digitSum p n := by
  intro f
  induction f with
  | zero => intro n h; simp at h; subst h; simp [dsumF]
  | succ f ih =>
    intro n h
    rw [dsumF, ih (n / p) ?_, ← digitSum_eq hp n]
    rw [pow_succ] at h
    exact Nat.div_lt_of_lt_mul (by rwa [mul_comm] at h)

/-- Digit sum, correct for `n < 4096`. -/
def dsum (p n : ℕ) : ℕ := dsumF p 12 n

theorem dsum_eq {p n : ℕ} (hp : 2 ≤ p) (hn : n < 4096) : dsum p n = digitSum p n := by
  apply dsumF_eq hp
  calc n < 4096 := hn
    _ = 2 ^ 12 := by norm_num
    _ ≤ p ^ 12 := Nat.pow_le_pow_left hp 12

/-- `List.countP`, written with `List.rec`. -/
def countR (f : ℕ → Bool) (l : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun a _ ih => (bif f a then 1 else 0) + ih) l

theorem countR_eq (f : ℕ → Bool) (l : List ℕ) : countR f l = (l.filter f).length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    change (bif f a then 1 else 0) + countR f l = _
    rw [ih, List.filter_cons]
    cases f a <;> simp [Nat.add_comm]

/-- Is `p` good for `n`, i.e. `p > √n` and `s_p(n) ≥ p`? -/
def goodB (n p : ℕ) : Bool := Nat.blt n (p * p) && Nat.ble p (n / p + n % p)

theorem trial_pairwise : Data.trial.Pairwise (· < ·) := pairwise_of_incr trial_incr

theorem trial_isPrime : allR isPrime Data.trial = true := by decide +kernel

theorem prime_of_mem_trial {p : ℕ} (hp : p ∈ Data.trial) : p.Prime :=
  prime_of_isPrime trial_pairwise (allR_eq_true.mp trial_isPrime p hp)

theorem card_goodPrimes_ge (n : ℕ) : countR (goodB n) Data.trial ≤ (goodPrimes n).card := by
  rw [countR_eq, ← List.toFinset_card_of_nodup ((trial_pairwise.imp Nat.ne_of_lt).filter _)]
  apply Finset.card_le_card
  intro p hp
  rw [List.mem_toFinset, List.mem_filter] at hp
  obtain ⟨h1, h2⟩ := hp
  unfold goodB at h2
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at h2
  rw [mem_goodPrimes]
  exact ⟨prime_of_mem_trial h1, h2⟩

theorem goodPrimes_subset_trial {n : ℕ} (hn : n < 2030) : goodPrimes n ⊆ Data.trial.toFinset := by
  intro p hp
  unfold goodPrimes at hp
  rw [Finset.mem_filter, Finset.mem_range] at hp
  rw [List.mem_toFinset]
  exact mem_trial hp.2.1 (by omega)

theorem card_goodPrimes_le {n : ℕ} (hn : n < 2030) :
    (goodPrimes n).card ≤ countR (goodB n) Data.trial := by
  rw [countR_eq, ← List.toFinset_card_of_nodup ((trial_pairwise.imp Nat.ne_of_lt).filter _)]
  apply Finset.card_le_card
  intro p hp
  have hp' := goodPrimes_subset_trial hn hp
  rw [mem_goodPrimes] at hp
  rw [List.mem_toFinset] at hp' ⊢
  rw [List.mem_filter]
  refine ⟨hp', ?_⟩
  unfold goodB
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq]
  exact hp.2

/-- Lower bounds for the number of good primes for `n ≤ 2014`: at least one if `n > 192` and at least
two if `n > 1080`.  (The exact values at `n = 192, 1080, 2014` are `card_goodPrimes_192` etc. below.) -/
def goodTable : Bool :=
  (List.range 2015).all fun n =>
    Nat.ble (bif Nat.blt 1080 n then 2 else bif Nat.blt 192 n then 1 else 0)
      (countR (goodB n) Data.trial)

theorem goodTable_true : goodTable = true := by decide +kernel

theorem two_good_of_lt {n : ℕ} (h1 : 1080 < n) (h2 : n ≤ 2014) : 2 ≤ (goodPrimes n).card := by
  have h := List.all_eq_true.mp goodTable_true n (List.mem_range.mpr (by omega))
  have e1 : Nat.blt 1080 n = true := Nat.blt_eq.mpr (by omega)
  rw [e1] at h
  simp only [Bool.cond_true, Nat.ble_eq] at h
  exact h.trans (card_goodPrimes_ge n)

theorem one_good_of_lt {n : ℕ} (h1 : 192 < n) (h2 : n ≤ 2014) : 1 ≤ (goodPrimes n).card := by
  rcases Nat.lt_or_ge 1080 n with h3 | h3
  · exact le_trans (by norm_num) (two_good_of_lt h3 h2)
  have h := List.all_eq_true.mp goodTable_true n (List.mem_range.mpr (by omega))
  have e1 : Nat.blt 1080 n = false := Bool.eq_false_iff.mpr (fun h => by rw [Nat.blt_eq] at h; omega)
  have e2 : Nat.blt 192 n = true := Nat.blt_eq.mpr (by omega)
  rw [e1, e2] at h
  simp only [Bool.cond_false, Bool.cond_true, Nat.ble_eq] at h
  exact h.trans (card_goodPrimes_ge n)

/-- For `n < 2030` the number of good primes is computed exactly by the list `Data.trial`. -/
theorem card_goodPrimes_eq {n : ℕ} (hn : n < 2030) :
    (goodPrimes n).card = countR (goodB n) Data.trial :=
  le_antisymm (card_goodPrimes_le hn) (card_goodPrimes_ge n)

theorem card_goodPrimes_192 : (goodPrimes 192).card = 0 := by
  rw [card_goodPrimes_eq (by norm_num)]; decide +kernel

theorem card_goodPrimes_1080 : (goodPrimes 1080).card = 1 := by
  rw [card_goodPrimes_eq (by norm_num)]; decide +kernel

theorem card_goodPrimes_2014 : (goodPrimes 2014).card = 2 := by
  rw [card_goodPrimes_eq (by norm_num)]; decide +kernel

/-- The exceptions: exactly these `n ≤ 192` have no good prime. -/
def exceptions : List ℕ :=
  [1, 2, 4, 6, 10, 11, 12, 15, 16, 28, 29, 30, 35, 36, 58, 59, 60, 69, 70, 78, 79, 80, 174, 190, 191,
    192]

def exceptionTable : Bool :=
  (List.range' 1 192).all fun n => (countR (goodB n) Data.trial == 0) == exceptions.contains n

theorem exceptionTable_true : exceptionTable = true := by decide +kernel

theorem goodPrimes_eq_empty_iff {n : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ 192) :
    goodPrimes n = ∅ ↔ n ∈ exceptions := by
  have h := List.all_eq_true.mp exceptionTable_true n (List.mem_range'.mpr ⟨n - 1, by omega, by omega⟩)
  rw [beq_iff_eq, Bool.eq_iff_iff, beq_iff_eq, List.contains_iff_mem] at h
  rw [← h, ← Finset.card_eq_zero]
  constructor
  · intro h0
    have := card_goodPrimes_ge n
    omega
  · intro h0
    have := card_goodPrimes_le (n := n) (by omega)
    omega

/-! ## The criteria for `n ≤ 2016` -/

/-- `∀ p, p ∣ D ∨ s_p(m) < p`, checked over the primes up to `m`. -/
def critB (D m : ℕ) : Bool :=
  allR (fun p => Nat.blt m p || Nat.beq (D % p) 0 || Nat.blt (dsum p m) p) Data.trial

theorem critB_iff {D m : ℕ} (hm : m < 2030) :
    critB D m = true ↔ ∀ p, p.Prime → p ∣ D ∨ digitSum p m < p := by
  unfold critB
  rw [allR_eq_true]
  constructor
  · intro h p hp
    rcases Nat.lt_or_ge m p with hmp | hmp
    · right; rw [digitSum_of_lt hp.two_le hmp]; exact hmp
    · have h1 := h p (mem_trial hp (by omega))
      simp only [Bool.or_eq_true, Nat.blt_eq, Nat.beq_eq] at h1
      rcases h1 with (h1 | h1) | h1
      · omega
      · left; exact Nat.dvd_of_mod_eq_zero h1
      · right; rwa [dsum_eq hp.two_le (by omega)] at h1
  · intro h p hp
    have hpp := prime_of_mem_trial hp
    simp only [Bool.or_eq_true, Nat.blt_eq, Nat.beq_eq]
    rcases Nat.lt_or_ge m p with hmp | hmp
    · left; left; exact hmp
    · rcases h p hpp with h1 | h1
      · left; right; exact Nat.mod_eq_zero_of_dvd h1
      · right; rwa [dsum_eq hpp.two_le (by omega)]

/-- The sets `S̄_k` for `k = 1, 2, 3`. -/
def S1 : List ℕ := [1, 2, 4, 6, 10, 12, 28, 30, 36, 60]
def S2 : List ℕ := [1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 15, 16, 21, 25, 28, 29, 30, 31, 36, 37, 55,
  57, 60, 61, 70, 121, 190]
def S3 : List ℕ := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22, 25, 26,
  28, 29, 30, 31, 32, 35, 36, 37, 38, 42, 50, 52, 55, 56, 57, 58, 60, 61, 62, 66, 70, 71, 72, 78, 80,
  92, 110, 121, 122, 156, 176, 177, 190, 191, 210, 392]

def derivTable (k : ℕ) (S : List ℕ) (N : ℕ) : Bool :=
  (List.range' k (N + 1 - k)).all fun n => critB (n.descFactorial k) (n - k + 1) == S.contains n

theorem derivTable1 : derivTable 1 S1 2016 = true := by decide +kernel
theorem derivTable2 : derivTable 2 S2 2016 = true := by decide +kernel
theorem derivTable3 : derivTable 3 S3 2016 = true := by decide +kernel

/-! ## The other tables -/

/-- `n ≤ 1080`: the primes with `s_p(n) ≥ p` are exactly the primes dividing `n + 1`. -/
def radicalTable : Bool :=
  (List.range' 1 1080).all fun n =>
    allR (fun p => Nat.blt (n + 1) p || (Nat.ble p (dsum p n) == Nat.beq ((n + 1) % p) 0)) Data.trial ==
      [3, 5, 8, 9, 11, 27, 29, 35, 59].contains n

theorem radicalTable_true : radicalTable = true := by decide +kernel

/-- `192 < n ≤ 1080`: some prime `p` with `s_p(n) ≥ p` and `(n + 1) ^ 2 < n p ^ 2`. -/
def lambdaTable : Bool :=
  (List.range' 193 888).all fun n =>
    Data.trial.any fun p => Nat.ble p (dsum p n) && Nat.blt ((n + 1) * (n + 1)) (n * (p * p))

theorem lambdaTable_true : lambdaTable = true := by decide +kernel

/-- `78 < k ≤ 192`: some prime `p ≥ 3` whose last two base-`p` digits of `k` add up to `≥ p`. -/
def alekseyevTable : Bool :=
  (List.range' 79 114).all fun k =>
    Data.trial.any fun p => Nat.ble 3 p && Nat.ble p (k % p + (k / p) % p)

theorem alekseyevTable_true : alekseyevTable = true := by decide +kernel

end KellnerBernoulli
