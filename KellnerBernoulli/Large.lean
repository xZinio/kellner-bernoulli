import KellnerBernoulli.Finite

/-!
# Large `n`

The only external input of the whole development is the following theorem of Rosser and Schoenfeld
(Math. Comp. 29 (1975), 243-269), which is not available in Mathlib.  It is *not* assumed as an axiom:
it appears as an explicit hypothesis `h : ThetaBound` of the theorems which use it.
-/

open Chebyshev

namespace KellnerBernoulli

/-- `|θ(x) - x| ≤ x / (40 log x)` for `x ≥ 4 * 10 ^ 6`, where `θ(x) = ∑_{p ≤ x} log p`.

Rosser and Schoenfeld proved this, with strict inequality, for all `x ≥ 678407` (Math. Comp. 29 (1975),
Corollary 2, (5.7); see also Broadbent, Kadiri, Lumley, Ng and Wilk, Math. Comp. 90 (2021), Table 2).
It also follows from `|θ(x) - x| < 0.2 x / log² x` for `x ≥ 3594641` (Dusart, Ramanujan J. 45 (2018),
Theorem 4.2), because `log x ≥ 8`.  Both published results are unconditional. -/
def ThetaBound : Prop :=
  ∀ x : ℝ, 4000000 ≤ x → |θ x - x| ≤ x / (40 * Real.log x)

/-- The theorem of Rosser and Schoenfeld as published. -/
def RosserSchoenfeld : Prop :=
  ∀ x : ℝ, 678407 ≤ x → |θ x - x| < x / (40 * Real.log x)

/-- Dusart's theorem. -/
def Dusart : Prop :=
  ∀ x : ℝ, 3594641 ≤ x → |θ x - x| < 0.2 * x / (Real.log x) ^ 2

theorem ThetaBound.of_rosserSchoenfeld (h : RosserSchoenfeld) : ThetaBound :=
  fun x hx => (h x (by linarith)).le

theorem log_ge_fifteen {x : ℝ} (hx : 4000000 ≤ x) : 15 ≤ Real.log x := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have h1 : Real.exp 15 = (Real.exp 1) ^ 15 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h2 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h3 : (Real.exp 1) ^ 15 ≤ 2.7182818286 ^ 15 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le h2.le 15
  rw [h1]
  refine h3.trans (le_trans ?_ hx)
  norm_num

theorem ThetaBound.of_dusart (h : Dusart) : ThetaBound := by
  intro x hx
  have hl := log_ge_fifteen hx
  refine (h x (by linarith)).le.trans ?_
  have hlpos : 0 < Real.log x := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hx0 : 0 < x := by linarith
  nlinarith [mul_pos hx0 hlpos]

/-- `log² x ≤ 16 √x`. -/
theorem log_sq_le {x : ℝ} (hx : 1 ≤ x) : (Real.log x) ^ 2 ≤ 16 * Real.sqrt x := by
  have hx0 : 0 < x := by linarith
  set y := Real.sqrt (Real.sqrt x) with hy
  have hs : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hy0 : 0 < y := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hx0)
  have hy2 : y ^ 2 = Real.sqrt x := Real.sq_sqrt hs
  have hy4 : y ^ 4 = x := by
    calc y ^ 4 = (y ^ 2) ^ 2 := by ring
      _ = x := by rw [hy2, Real.sq_sqrt hx0.le]
  have hlog : Real.log x = 4 * Real.log y := by
    rw [← hy4, Real.log_pow]; norm_num
  have h1 : Real.log y ≤ y := by
    have := Real.log_le_sub_one_of_pos hy0; linarith
  have h0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have h2 : 0 ≤ Real.log y := by linarith
  rw [hlog, ← hy2]
  nlinarith

/-- Primes in `(s, s + U]`. -/
def primesIn (s U : ℕ) : Finset ℕ := (Finset.Ioc s (s + U)).filter Nat.Prime

theorem theta_add_sub (s U : ℕ) :
    θ ((s + U : ℕ) : ℝ) - θ (s : ℝ) = ∑ p ∈ primesIn s U, Real.log p := by
  have hd : (Finset.Ioc 0 (s + U)).filter Nat.Prime
      = (Finset.Ioc 0 s).filter Nat.Prime ∪ primesIn s U := by
    ext p
    simp only [primesIn, Finset.mem_filter, Finset.mem_union, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      by_cases h : p ≤ s
      · exact Or.inl ⟨⟨h1, h⟩, h3⟩
      · exact Or.inr ⟨⟨by omega, h2⟩, h3⟩
    · rintro (⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩)
      · exact ⟨⟨h1, by omega⟩, h3⟩
      · exact ⟨⟨by omega, h2⟩, h3⟩
  have hdisj : Disjoint ((Finset.Ioc 0 s).filter Nat.Prime) (primesIn s U) := by
    rw [Finset.disjoint_left]
    intro p hp hp'
    simp only [primesIn, Finset.mem_filter, Finset.mem_Ioc] at hp hp'
    omega
  unfold theta
  rw [Nat.floor_natCast, Nat.floor_natCast, hd, Finset.sum_union hdisj]
  ring

theorem sum_log_le (s U : ℕ) :
    ∑ p ∈ primesIn s U, Real.log p ≤ (primesIn s U).card * Real.log ((s + U : ℕ) : ℝ) := by
  rw [← nsmul_eq_mul]
  apply Finset.sum_le_card_nsmul
  intro p hp
  simp only [primesIn, Finset.mem_filter, Finset.mem_Ioc] at hp
  apply Real.log_le_log
  · have : 0 < p := hp.2.pos
    exact_mod_cast this
  · exact_mod_cast hp.1.2

set_option maxHeartbeats 1000000 in
/-- The main estimate: for `s ≥ 4 * 10 ^ 6` there is `U` with enough primes in `(s, s + U]`. -/
theorem exists_many_primes (h : ThetaBound) {s : ℕ} (hs : 4000000 ≤ s) :
    ∃ U : ℕ, 1 ≤ U ∧
      2 * U ^ 2 + 8 * (s + U) < (primesIn s U).card * (s + U) := by
  set S : ℝ := (s : ℝ) with hS
  have hS4 : (4000000 : ℝ) ≤ S := by rw [hS]; exact_mod_cast hs
  have hSpos : 0 < S := by linarith
  set l : ℝ := Real.log S with hl
  have hl15 : 15 ≤ l := log_ge_fifteen hS4
  have hlpos : 0 < l := by linarith
  have hlsq : l ^ 2 ≤ 16 * Real.sqrt S := log_sq_le (by linarith)
  have hsqrt : 2000 ≤ Real.sqrt S := by
    apply Real.le_sqrt_of_sq_le
    norm_num; linarith
  have hSsqrt : Real.sqrt S * Real.sqrt S = S := Real.mul_self_sqrt hSpos.le
  -- `S ≥ 125 l²`
  have hSl : 125 * l ^ 2 ≤ S := by nlinarith
  set U : ℕ := ⌊S / (4 * l)⌋₊ with hU
  have hq0 : 0 ≤ S / (4 * l) := by positivity
  have hU1 : (U : ℝ) ≤ S / (4 * l) := Nat.floor_le hq0
  have hU2 : S / (4 * l) < U + 1 := Nat.lt_floor_add_one _
  have hbig : 400 ≤ S / (4 * l) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hUpos : 1 ≤ U := by
    have : (1 : ℝ) ≤ (U : ℝ) := by linarith
    exact_mod_cast this
  refine ⟨U, hUpos, ?_⟩
  set u : ℝ := (U : ℝ) with hu
  have hu0 : 0 ≤ u := by positivity
  set E : ℝ := S + u with hE
  have hEcast : ((s + U : ℕ) : ℝ) = E := by rw [hE, hS, hu]; push_cast; ring
  have hES : S ≤ E := by linarith
  have hEpos : 0 < E := by linarith
  -- the logarithm of `s + U`
  have huS : u * (4 * l) ≤ S := by
    rw [le_div_iff₀ (by positivity)] at hU1; exact hU1
  have hlogE : Real.log E ≤ l + u / S := by
    have h1 : E = S * (1 + u / S) := by field_simp; rw [hE]
    have h2 : 0 < 1 + u / S := by positivity
    rw [h1, Real.log_mul hSpos.ne' h2.ne']
    have := Real.log_le_sub_one_of_pos h2
    linarith
  have hlogE' : l ≤ Real.log E := Real.log_le_log hSpos hES
  -- theta bounds
  have hb1 := h E (by linarith)
  have hb2 := h S hS4
  rw [abs_le] at hb1 hb2
  have hbE : E / (40 * Real.log E) ≤ E / (40 * l) := by
    apply div_le_div_of_nonneg_left hEpos.le (by positivity)
    linarith
  have hdiff := theta_add_sub s U
  have hsum := sum_log_le s U
  rw [hEcast] at hdiff hsum
  set c : ℝ := ((primesIn s U).card : ℝ) with hc
  have hc0 : 0 ≤ c := by positivity
  -- `u - (2 S + u) / (40 l) ≤ c (l + u / S)`
  have hkey : u - E / (40 * l) - S / (40 * l) ≤ c * (l + u / S) := by
    have h1 : θ E - θ S ≤ c * Real.log E := by rw [hdiff]; exact hsum
    have h2 : c * Real.log E ≤ c * (l + u / S) := mul_le_mul_of_nonneg_left hlogE hc0
    have h3 : S / (40 * Real.log S) = S / (40 * l) := rfl
    linarith [hb1.1, hb2.2]
  -- it suffices to bound `c` from below
  have hgoal : 2 * u ^ 2 / S + 8 < c := by
    by_contra hcon
    rw [not_lt] at hcon
    -- upper bound for `c`
    have hu2 : u ^ 2 ≤ (S / (4 * l)) ^ 2 := pow_le_pow_left₀ hu0 hU1 2
    have hc1 : c ≤ S / (8 * l ^ 2) + 8 := by
      have : 2 * u ^ 2 / S ≤ S / (8 * l ^ 2) := by
        rw [div_le_div_iff₀ hSpos (by positivity)]
        have : (S / (4 * l)) ^ 2 * (16 * l ^ 2) = S ^ 2 := by field_simp; ring
        nlinarith [sq_nonneg l]
      linarith
    have huS' : u / S ≤ 1 / (4 * l) := by
      rw [div_le_div_iff₀ hSpos (by positivity)]
      linarith
    have hfac : l + u / S ≤ l + 1 / (4 * l) := by linarith
    have hup : c * (l + u / S) ≤ (S / (8 * l ^ 2) + 8) * (l + 1 / (4 * l)) := by
      apply mul_le_mul hc1 hfac (by positivity) (by positivity)
    have hlow : S / (4 * l) - 1 - (2 * S + S / (4 * l)) / (40 * l)
        ≤ u - E / (40 * l) - S / (40 * l) := by
      have h1 : E / (40 * l) + S / (40 * l) ≤ (2 * S + S / (4 * l)) / (40 * l) := by
        rw [← add_div]
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith
      linarith
    have hfinal : S / (4 * l) - 1 - (2 * S + S / (4 * l)) / (40 * l)
        ≤ (S / (8 * l ^ 2) + 8) * (l + 1 / (4 * l)) := by linarith
    -- multiply by `l³`
    have e1 : (S / (4 * l) - 1 - (2 * S + S / (4 * l)) / (40 * l)) * l ^ 3
        = S * l ^ 2 / 5 - l ^ 3 - S * l / 160 := by field_simp; ring
    have e2 : ((S / (8 * l ^ 2) + 8) * (l + 1 / (4 * l))) * l ^ 3
        = S * l ^ 2 / 8 + S / 32 + 8 * l ^ 4 + 2 * l ^ 2 := by field_simp; ring
    have hmul := mul_le_mul_of_nonneg_right hfinal (by positivity : 0 ≤ l ^ 3)
    rw [e1, e2] at hmul
    -- contradiction with `125 l² ≤ S`, `l ≥ 15`
    have k1 : 125 * (l ^ 2 * l ^ 2) ≤ S * l ^ 2 := by nlinarith
    have hl2 : 225 ≤ l ^ 2 := by nlinarith
    have k2 : S * l * 15 ≤ S * l ^ 2 := by nlinarith
    have k3 : S * 225 ≤ S * l ^ 2 := by nlinarith
    have k4 : l ^ 3 * 15 ≤ l ^ 2 * l ^ 2 := by nlinarith
    have k5 : l ^ 2 * 225 ≤ l ^ 2 * l ^ 2 := by nlinarith
    have k6 : l ^ 4 = l ^ 2 * l ^ 2 := by ring
    have k7 : 0 < l ^ 2 * l ^ 2 := by positivity
    rw [k6] at hmul
    linarith
  -- back to natural numbers
  have hreal : 2 * u ^ 2 + 8 * E < c * E := by
    have h1 : 2 * u ^ 2 / E ≤ 2 * u ^ 2 / S :=
      div_le_div_of_nonneg_left (by positivity) hSpos hES
    have h2 : 2 * u ^ 2 / E + 8 < c := by linarith
    have h3 := mul_lt_mul_of_pos_right h2 hEpos
    have h4 : (2 * u ^ 2 / E + 8) * E = 2 * u ^ 2 + 8 * E := by field_simp
    linarith
  have e1 : ((2 * U ^ 2 + 8 * (s + U) : ℕ) : ℝ) = 2 * u ^ 2 + 8 * E := by
    rw [hE, hS, hu]; push_cast; ring
  have e2 : (((primesIn s U).card * (s + U) : ℕ) : ℝ) = c * E := by
    rw [hc, hE, hS, hu]; push_cast; ring
  have hnat : ((2 * U ^ 2 + 8 * (s + U) : ℕ) : ℝ) < (((primesIn s U).card * (s + U) : ℕ) : ℝ) := by
    rw [e1, e2]; exact hreal
  exact_mod_cast hnat

end KellnerBernoulli
