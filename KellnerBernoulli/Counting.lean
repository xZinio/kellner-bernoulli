import Mathlib

/-!
# The counting lemma

For `n ≥ 1` and `s = ⌊√n⌋`, all but a few of the integers `m` slightly larger than `s` have
base-`m` digit sum at least `m` (Lemmas 7 and 8 of the paper).  `card_bad_mul_lt` is Lemma 8 with the
constant `4` of the paper: fewer than `4 + 2 U² / (s + U)` of the integers `s + 1, …, s + U` are bad.
-/

namespace KellnerBernoulli

/-- The sum of the base-`b` digits of `n`. -/
abbrev digitSum (b n : ℕ) : ℕ := (Nat.digits b n).sum

/-- A number `n < m ^ 2` has at most two digits in base `m`. -/
theorem digitSum_of_lt_sq {m n : ℕ} (hm : 2 ≤ m) (h : n < m ^ 2) :
    digitSum m n = n / m + n % m := by
  have hdiv : n / m < m := Nat.div_lt_of_lt_mul (by nlinarith)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [digitSum]
  · unfold digitSum
    rw [Nat.digits_def' (by omega) hn]
    rcases Nat.eq_zero_or_pos (n / m) with h0 | hpos
    · simp [h0]
    · rw [Nat.digits_of_lt m (n / m) hpos.ne' hdiv]
      simp [add_comm]

/-- `m` is *bad* for `n` if `⌊n / m⌋ + (n mod m) < m`. -/
def Bad (n m : ℕ) : Prop := n / m + n % m < m

instance (n m : ℕ) : Decidable (Bad n m) := inferInstanceAs (Decidable (_ < _))

/-- Lemma 7, first part: the quotients `⌊n / m⌋` drop by at most one. -/
theorem div_pred_le {n s m : ℕ} (hs : n < (s + 1) * (s + 1)) (hm : s + 2 ≤ m) :
    n / (m - 1) ≤ n / m + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hk : s + 1 ≤ k := by omega
  have hkpos : 0 < k := by omega
  set q := n / (k + 1) with hq
  have h1 : n < (k + 1) * (q + 1) := by
    have := Nat.lt_mul_div_succ n (show 0 < k + 1 by omega)
    simpa [hq] using this
  have hqk : q + 1 ≤ k := by
    have : n < k * k := lt_of_lt_of_le hs (Nat.mul_le_mul hk hk)
    have h2 : q < k := by
      rw [hq]
      exact Nat.div_lt_of_lt_mul (by nlinarith)
    omega
  have h3 : n < k * (q + 2) := by nlinarith
  have : n / k < q + 2 := Nat.div_lt_of_lt_mul (by simpa using h3)
  omega

/-- Lemma 7, second part: a bad `m ≥ s + 2` has `⌊n/(m-1)⌋ = ⌊n/m⌋`, or `m - 1` divides `n`. -/
theorem bad_imp {n m : ℕ} (hm : 2 ≤ m) (h : Bad n m) :
    n / (m - 1) = n / m ∨ (m - 1) ∣ n := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hkpos : 0 < k := by omega
  unfold Bad at h
  set q := n / (k + 1) with hq
  have hdm := Nat.div_add_mod n (k + 1)
  rw [← hq] at hdm
  have h1 : n ≤ k * (q + 1) := by nlinarith
  rcases Nat.lt_or_ge n (k * (q + 1)) with hlt | hge
  · left
    have h2 : n / k < q + 1 := Nat.div_lt_of_lt_mul hlt
    have h3 : q ≤ n / k := by
      rw [hq]
      exact Nat.div_le_div_left (by omega) hkpos
    omega
  · right
    exact ⟨q + 1, by omega⟩

/-- Part (a) of Lemma 8: telescoping. -/
theorem card_flat_add {n s : ℕ} (hs : n < (s + 1) * (s + 1)) (U : ℕ) :
    ((Finset.Ioc (s + 1) (s + 1 + U)).filter (fun m => n / (m - 1) = n / m)).card + n / (s + 1)
      ≤ U + n / (s + 1 + U) := by
  induction U with
  | zero => simp
  | succ U ih =>
    have hIoc : Finset.Ioc (s + 1) (s + 1 + (U + 1))
        = insert (s + 1 + U + 1) (Finset.Ioc (s + 1) (s + 1 + U)) := by
      ext a; simp only [Finset.mem_Ioc, Finset.mem_insert]; omega
    have hdrop := div_pred_le (n := n) (s := s) (m := s + 1 + U + 1) hs (by omega)
    simp only [Nat.add_sub_cancel] at hdrop
    rw [hIoc, Finset.filter_insert]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (by simp)]
      simp only [Nat.add_sub_cancel] at h
      have h' : n / (s + 1 + (U + 1)) = n / (s + 1 + U) := by
        rw [h, ← Nat.add_assoc]
      omega
    · have h' : n / (s + 1 + (U + 1)) = n / (s + 1 + U + 1) := by rw [← Nat.add_assoc]
      omega

/-- If `t² ≥ 4 n`, then `2 s E + n ≤ t E + s²` (where `s = ⌊√n⌋ < E`). -/
theorem two_mul_le_of_sq {n s E t : ℕ} (hs1 : s * s ≤ n) (hs2 : n < (s + 1) * (s + 1))
    (hE : s + 1 ≤ E) (ht : 4 * n ≤ t * t) : 2 * s * E + n ≤ t * E + s * s := by
  by_contra hcon
  obtain ⟨r, rfl⟩ : ∃ r, n = s * s + r := ⟨n - s * s, by omega⟩
  have hr : r ≤ 2 * s := by nlinarith
  have h1 : t * E < 2 * s * E + r := by omega
  have h2 : (t * E) * (t * E) < (2 * s * E + r) * (2 * s * E + r) := Nat.mul_self_lt_mul_self h1
  have h3 : 4 * (s * s + r) * (E * E) ≤ (t * E) * (t * E) := by
    have := Nat.mul_le_mul_right (E * E) ht
    calc 4 * (s * s + r) * (E * E) ≤ t * t * (E * E) := this
      _ = (t * E) * (t * E) := by ring
  have h4 : 4 * s * E + r ≤ 4 * E * E := by nlinarith
  have h5 : r * (4 * s * E + r) ≤ r * (4 * E * E) := Nat.mul_le_mul_left r h4
  nlinarith

/-- Part (b) of Lemma 8: the divisors of `n` in `(s, E)`; at most `1 + (E - s)² / E` of them. -/
theorem card_divisors_mul_le {n s E : ℕ} (hs1 : s * s ≤ n) (hs2 : n < (s + 1) * (s + 1))
    (hE : s + 1 ≤ E) :
    ((Finset.Ico (s + 1) E).filter (fun d => d ∣ n)).card * E + 2 * s * E
      ≤ E * E + s * s + E := by
  classical
  set D := (Finset.Ico (s + 1) E).filter (fun d => d ∣ n) with hD
  have hEpos : 0 < E := by omega
  -- the lower end of the range of `d ↦ d + n / d`
  obtain ⟨X, hX⟩ : ∃ X, 2 * s * E + n = X + s * s := ⟨2 * s * E + n - s * s, by omega⟩
  set L := (X + E - 1) / E with hL
  have hLE : X ≤ L * E := by
    have h1 := Nat.div_add_mod (X + E - 1) E
    have h2 := Nat.mod_lt (X + E - 1) hEpos
    rw [← hL] at h1
    have : X ≤ E * L := by omega
    rw [Nat.mul_comm]; exact this
  have hmaps : ∀ d ∈ D, d + n / d ∈ Finset.Icc L (E + n / E) := by
    intro d hd
    rw [hD, Finset.mem_filter, Finset.mem_Ico] at hd
    obtain ⟨⟨hd1, hd2⟩, hdvd⟩ := hd
    obtain ⟨k, hk⟩ := hdvd
    have hdpos : 0 < d := by omega
    have hndiv : n / d = k := by rw [hk]; exact Nat.mul_div_cancel_left k hdpos
    rw [hndiv, Finset.mem_Icc]
    constructor
    · -- `(d + k)² ≥ 4 d k = 4 n`, so `(d + k) E + s² ≥ 2 s E + n`
      have hsq : 4 * n ≤ (d + k) * (d + k) := by
        rw [hk]; zify; nlinarith [sq_nonneg ((d : ℤ) - k)]
      have key := two_mul_le_of_sq hs1 hs2 hE hsq
      have key2 : X ≤ E * (d + k) := by rw [Nat.mul_comm]; omega
      rw [hL, Nat.div_le_iff_le_mul_add_pred hEpos]
      omega
    · have hkd : k ≤ d := by
        by_contra hcon
        replace hcon := not_le.mp hcon
        nlinarith
      by_cases hdkE : d + k ≤ E
      · exact le_trans hdkE (Nat.le_add_right _ _)
      · replace hdkE := not_le.mp hdkE
        have : (d + k - E) * E ≤ n := by
          obtain ⟨j, hj⟩ : ∃ j, d + k = E + j := ⟨d + k - E, by omega⟩
          have hjj : d + k - E = j := by omega
          rw [hjj]
          have hE' : k ≤ E := by omega
          have : (E - d : ℤ) * (E - k) ≥ 0 := by
            apply mul_nonneg <;> omega
          zify at hj ⊢
          rw [hk]
          push_cast
          nlinarith
        have := (Nat.le_div_iff_mul_le hEpos).mpr this
        omega
  have hinj : Set.InjOn (fun d => d + n / d) (D : Set ℕ) := by
    intro d hd d' hd' heq
    rw [hD, Finset.coe_filter] at hd hd'
    simp only [Finset.mem_Ico, Set.mem_ofPred_eq] at hd hd'
    obtain ⟨⟨hd1, hd2⟩, ⟨k, hk⟩⟩ := hd
    obtain ⟨⟨hd1', hd2'⟩, ⟨k', hk'⟩⟩ := hd'
    have hdpos : 0 < d := by omega
    have hdpos' : 0 < d' := by omega
    have e1 : n / d = k := by rw [hk]; exact Nat.mul_div_cancel_left k hdpos
    have e2 : n / d' = k' := by rw [hk']; exact Nat.mul_div_cancel_left k' hdpos'
    simp only [e1, e2] at heq
    have hk_le : k ≤ s := by
      by_contra hcon
      replace hcon := not_le.mp hcon
      nlinarith
    have hzero : ((d' : ℤ) - d) * ((d' : ℤ) - k) = 0 := by
      have h1 : (d : ℤ) + k = d' + k' := by exact_mod_cast heq
      have h2 : (d : ℤ) * k = d' * k' := by exact_mod_cast hk.symm.trans hk'
      have : ((d' : ℤ) - d) * ((d' : ℤ) - k) = d' * d' - d' * (d + k) + d * k := by ring
      rw [this, h1, h2]; ring
    rcases mul_eq_zero.mp hzero with h | h
    · omega
    · omega
  have hcard : D.card ≤ (Finset.Icc L (E + n / E)).card :=
    Finset.card_le_card_of_injOn _ hmaps hinj
  rw [Nat.card_Icc] at hcard
  have hmod : n / E * E ≤ n := Nat.div_mul_le_self n E
  rcases Nat.lt_or_ge (E + n / E + 1) L with hlt | hge
  · have h0 : D.card = 0 := by omega
    rw [h0]
    nlinarith [sq_nonneg ((E : ℤ) - s)]
  · have h1 : D.card + L ≤ E + n / E + 1 := by omega
    have h2 : (D.card + L) * E ≤ (E + n / E + 1) * E := Nat.mul_le_mul_right E h1
    nlinarith [h2, hLE, hX, hmod]

/-- Lemma 8: fewer than `4 + 2 U² / (s + U)` of the integers `s + 1, …, s + U` are bad. -/
theorem card_bad_mul_lt {n s U : ℕ} (hs1 : s * s ≤ n) (hs2 : n < (s + 1) * (s + 1))
    (hspos : 1 ≤ s) (hU : 1 ≤ U) :
    ((Finset.Ioc s (s + U)).filter (fun m => Bad n m)).card * (s + U)
      < 2 * U ^ 2 + 4 * (s + U) := by
  classical
  set E := s + U with hE
  set A := (Finset.Ioc (s + 1) (s + 1 + (U - 1))).filter (fun m => n / (m - 1) = n / m) with hA
  set D := (Finset.Ico (s + 1) E).filter (fun d => d ∣ n) with hD
  have hsub : (Finset.Ioc s E).filter (fun m => Bad n m)
      ⊆ insert (s + 1) (A ∪ D.image (· + 1)) := by
    intro m hm
    rw [Finset.mem_filter, Finset.mem_Ioc] at hm
    obtain ⟨⟨hm1, hm2⟩, hbad⟩ := hm
    rw [Finset.mem_insert]
    by_cases h1 : m = s + 1
    · exact Or.inl h1
    · right
      rw [Finset.mem_union]
      rcases bad_imp (by omega) hbad with h | h
      · left
        rw [hA, Finset.mem_filter, Finset.mem_Ioc]
        exact ⟨⟨by omega, by omega⟩, h⟩
      · right
        rw [Finset.mem_image]
        refine ⟨m - 1, ?_, by omega⟩
        rw [hD, Finset.mem_filter, Finset.mem_Ico]
        exact ⟨⟨by omega, by omega⟩, h⟩
  have hcard : ((Finset.Ioc s E).filter (fun m => Bad n m)).card ≤ 1 + A.card + D.card := by
    calc _ ≤ (insert (s + 1) (A ∪ D.image (· + 1))).card := Finset.card_le_card hsub
      _ ≤ (A ∪ D.image (· + 1)).card + 1 := Finset.card_insert_le _ _
      _ ≤ A.card + (D.image (· + 1)).card + 1 := by
          have := Finset.card_union_le A (D.image (· + 1)); omega
      _ ≤ A.card + D.card + 1 := by
          have : (D.image (· + 1)).card ≤ D.card := Finset.card_image_le
          omega
      _ = 1 + A.card + D.card := by omega
  -- part (a): fewer than `2 + U² / E` flat steps
  have ha := card_flat_add hs2 (U - 1)
  rw [← hA] at ha
  have hEq : s + 1 + (U - 1) = E := by omega
  rw [hEq] at ha
  have hq1 : s - 1 ≤ n / (s + 1) := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    nlinarith
  have hmod : n / E * E ≤ n := Nat.div_mul_le_self n E
  have hA' : A.card + s ≤ U + n / E := by omega
  have hAmul : A.card * E + s * E ≤ U * E + n := by nlinarith
  -- part (b): at most `1 + U² / E` divisors
  have hb := card_divisors_mul_le (E := E) hs1 hs2 (by omega)
  rw [← hD] at hb
  have hn : n ≤ s * s + 2 * s := by nlinarith
  have h1 : ((Finset.Ioc s E).filter (fun m => Bad n m)).card * E
      ≤ (1 + A.card + D.card) * E := Nat.mul_le_mul_right _ hcard
  have hEs : E * E = s * s + 2 * s * U + U * U := by rw [hE]; ring
  have hsE : s * E = s * s + s * U := by rw [hE]; ring
  have hUE : U * E = s * U + U * U := by rw [hE]; ring
  nlinarith

end KellnerBernoulli
