import ThetaSum.Hypotheses

/-!
# Machine check of the finite range of Conjectures 1.1, 3.1, 3.2

Lemma 2.5 of the paper (`S_eq_lemma25`), the reciprocity for `F`, a fast evaluator `Sfast`
(Euclid-type recursion, `Sfast_eq : Sfast p = S p` for odd primes) and kernel-checked computations
(`decide +kernel`, no `native_decide`).
-/

open Finset

namespace ThetaSum

/-- `F(x, y) = ∑_{c=1}^{⌊(y-1)/2⌋} ⌊c x / y⌋` (Lemma 2.5). -/
def Ffl (x y : ℕ) : ℕ := ∑ c ∈ Icc 1 ((y - 1) / 2), c * x / y

lemma S'_eq (h k : ℕ) : S' h k = ∑ j ∈ Ico 1 k, (-1 : ℤ) ^ (j + 1 + h * j / k) := by
  unfold S'
  refine sum_congr rfl fun j _ => ?_
  rw [show ((h * j : ℚ)) = ((h * j : ℕ) : ℚ) by push_cast; ring, Nat.floor_div_eq_div]

lemma sum_Icc_id_two (U : ℕ) : 2 * ∑ c ∈ Icc 1 U, c = U * (U + 1) := by
  induction U with
  | zero => simp
  | succ n ih => rw [sum_Icc_succ_top (by omega), mul_add, ih]; ring

lemma sum_Icc_id (U : ℕ) : ∑ c ∈ Icc 1 U, c = U * (U + 1) / 2 := by
  rw [← sum_Icc_id_two U]; omega

/-- `F(q y + r, y) = q C(U+1, 2) + F(r, y)`. -/
lemma Ffl_add (q r y : ℕ) (hy : 0 < y) :
    Ffl (q * y + r) y = q * ((y - 1) / 2 * ((y - 1) / 2 + 1) / 2) + Ffl r y := by
  unfold Ffl
  rw [← sum_Icc_id, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun c _ => ?_
  rw [show c * (q * y + r) = c * r + (c * q) * y by ring, Nat.add_mul_div_right _ _ hy]
  ring

lemma count_le (C m : ℕ) (hm : m ≤ C) : ∑ c ∈ Icc 1 C, (if c ≤ m then 1 else 0) = m := by
  rw [sum_boole]
  have : (Icc 1 C).filter (fun c => c ≤ m) = Icc 1 m := by
    ext c; simp only [mem_filter, mem_Icc]; omega
  rw [this]; simp

/-- Lattice-point reciprocity: `∑_{b ≤ B} ⌊ab/q⌋ + ∑_{c ≤ C} ⌊qc/a⌋ = BC` when the line
`ab = qc` has no lattice point in `[1,B] × [1,C]` and the floors stay in range. -/
lemma lattice (a q B C : ℕ) (ha : 0 < a) (hq : 0 < q)
    (h1 : ∀ b ∈ Icc 1 B, a * b / q ≤ C) (h2 : ∀ c ∈ Icc 1 C, q * c / a ≤ B)
    (h3 : ∀ b ∈ Icc 1 B, ∀ c ∈ Icc 1 C, a * b ≠ q * c) :
    ∑ b ∈ Icc 1 B, a * b / q + ∑ c ∈ Icc 1 C, q * c / a = B * C := by
  have e1 : ∀ b ∈ Icc 1 B, a * b / q = ∑ c ∈ Icc 1 C, (if q * c ≤ a * b then 1 else 0) := by
    intro b hb
    rw [← count_le C (a * b / q) (h1 b hb)]
    refine sum_congr rfl fun c _ => ?_
    simp only [Nat.le_div_iff_mul_le hq, mul_comm c q]
  have e2 : ∀ c ∈ Icc 1 C, q * c / a = ∑ b ∈ Icc 1 B, (if a * b ≤ q * c then 1 else 0) := by
    intro c hc
    rw [← count_le B (q * c / a) (h2 c hc)]
    refine sum_congr rfl fun b _ => ?_
    simp only [Nat.le_div_iff_mul_le ha, mul_comm b a]
  rw [sum_congr rfl e1, sum_congr rfl e2, sum_comm (s := Icc 1 C), ← sum_add_distrib]
  have : ∀ b ∈ Icc 1 B, ∑ c ∈ Icc 1 C, (if q * c ≤ a * b then 1 else 0) +
      ∑ c ∈ Icc 1 C, (if a * b ≤ q * c then 1 else 0) = C := by
    intro b hb
    rw [← sum_add_distrib]
    have : ∀ c ∈ Icc 1 C, (if q * c ≤ a * b then 1 else 0) + (if a * b ≤ q * c then 1 else 0) = 1 := by
      intro c hc
      have := h3 b hb c hc
      split_ifs <;> omega
    rw [sum_congr rfl this]; simp
  rw [sum_congr rfl this]; simp

/-- If `x + y = a p` and `p ∤ x` then `⌊x/p⌋ + ⌊y/p⌋ + 1 = a`. -/
lemma div_add_div_succ (x y p a : ℕ) (hp : 0 < p) (hxy : x + y = a * p) (hx : ¬ p ∣ x) :
    x / p + y / p + 1 = a := by
  have hx1 := Nat.div_add_mod x p
  have hy1 := Nat.div_add_mod y p
  have hxm : 0 < x % p := Nat.pos_of_ne_zero (fun h => hx (Nat.dvd_of_mod_eq_zero h))
  have hym : 0 < y % p := by
    apply Nat.pos_of_ne_zero; intro h
    apply hx
    have hy : p ∣ y := Nat.dvd_of_mod_eq_zero h
    have : p ∣ x + y := by rw [hxy]; exact Dvd.intro_left a rfl
    exact (Nat.dvd_add_right hy).mp (by rwa [add_comm] at this)
  have hxl := Nat.mod_lt x hp
  have hyl := Nat.mod_lt y hp
  set s := x % p + y % p with hs
  have hsum : p * (x / p + y / p) + s = a * p := by rw [← hxy, hs]; linarith
  have hdvd : p ∣ s := by
    have : p ∣ p * (x / p + y / p) + s := by rw [hsum]; exact Dvd.intro_left a rfl
    exact (Nat.dvd_add_right (Dvd.intro _ rfl)).mp this
  obtain ⟨k, hk⟩ := hdvd
  have hk2 : k < 2 := by
    have : p * k < p * 2 := by rw [← hk]; omega
    exact Nat.lt_of_mul_lt_mul_left this
  have hk1 : k = 1 := by
    rcases Nat.lt_or_ge k 1 with h | h
    · have : k = 0 := by omega
      subst this; simp at hk; omega
    · omega
  subst hk1
  have : p * (x / p + y / p + 1) = p * a := by linarith
  exact Nat.eq_of_mul_eq_mul_left hp this

lemma floor_half (r b y U : ℕ) (hU : 2 * U < y) (hb : b ≤ U) :
    r * b / y ≤ (r - 1) / 2 := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr; simp
  set m := r * b / y
  have h1 : m * y ≤ r * b := Nat.div_mul_le_self _ _
  have h2 : r * b ≤ r * U := Nat.mul_le_mul_left r hb
  have h3 : (2 * m) * y < r * y := by nlinarith
  have := Nat.lt_of_mul_lt_mul_right h3
  omega

/-- Reciprocity: `F(r, y) + F(y, r) = ⌊(y-1)/2⌋ ⌊(r-1)/2⌋` for coprime `r, y ≥ 1`. -/
lemma Ffl_recip (r y : ℕ) (hr : 0 < r) (hy : 0 < y) (hco : Nat.Coprime r y) :
    Ffl r y + Ffl y r = (y - 1) / 2 * ((r - 1) / 2) := by
  have h := lattice r y ((y - 1) / 2) ((r - 1) / 2) hr hy
    (fun b hb => floor_half r b y ((y - 1) / 2) (by omega) (mem_Icc.mp hb).2)
    (fun c hc => floor_half y c r ((r - 1) / 2) (by omega) (mem_Icc.mp hc).2)
    (by
      intro b hb c _ he
      have hd : y ∣ r * b := ⟨c, he⟩
      have := Nat.le_of_dvd (mem_Icc.mp hb).1 (hco.symm.dvd_of_dvd_mul_left hd)
      have := (mem_Icc.mp hb).2
      omega)
  unfold Ffl
  rw [← h]
  congr 1
  · exact sum_congr rfl fun c _ => by rw [mul_comm]
  · exact sum_congr rfl fun c _ => by rw [mul_comm]

/-- `2 ∑_{b=1}^{p-1} ⌊ab/p⌋ + (p - 1) = a (p - 1)` for `p` prime, `p ∤ a`. -/
lemma sum_floor_ab (p a : ℕ) (hp : p.Prime) (ha : ¬ p ∣ a) :
    2 * ∑ b ∈ Ico 1 p, a * b / p + (p - 1) = a * (p - 1) := by
  have hp0 := hp.pos
  have hrefl : ∑ b ∈ Ico 1 p, a * b / p = ∑ b ∈ Ico 1 p, a * (p - b) / p := by
    apply sum_nbij' (fun b => p - b) (fun b => p - b)
    · intro b hb; simp only [mem_Ico] at hb ⊢; omega
    · intro b hb; simp only [mem_Ico] at hb ⊢; omega
    · intro b hb; simp only [mem_Ico] at hb; omega
    · intro b hb; simp only [mem_Ico] at hb; omega
    · intro b hb; simp only [mem_Ico] at hb; rw [Nat.sub_sub_self hb.2.le]
  have hterm : ∀ b ∈ Ico 1 p, a * b / p + a * (p - b) / p + 1 = a := by
    intro b hb
    simp only [mem_Ico] at hb
    apply div_add_div_succ _ _ p a hp0
    · rw [← mul_add, Nat.add_sub_cancel' hb.2.le]
    · intro hd
      rcases (Nat.Prime.dvd_mul hp).mp hd with h | h
      · exact ha h
      · have := Nat.le_of_dvd hb.1 h; omega
  have : 2 * ∑ b ∈ Ico 1 p, a * b / p + (p - 1) =
      ∑ b ∈ Ico 1 p, (a * b / p + a * (p - b) / p + 1) := by
    rw [sum_add_distrib, sum_add_distrib, ← hrefl]; simp; ring
  rw [this, sum_congr rfl hterm]; simp [mul_comm]

/-- `T(a) = ∑_{b=1}^{p-1} (-1)^{⌊ab/p⌋}`. -/
def Tq (p a : ℕ) : ℤ := ∑ b ∈ Ico 1 p, (-1 : ℤ) ^ (a * b / p)

lemma neg_one_pow_eq (m : ℕ) : (-1 : ℤ) ^ m = 1 - 2 * m + 4 * ((m / 2 : ℕ) : ℤ) := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' m
  · rw [pow_mul, neg_one_sq, one_pow, Nat.mul_div_cancel_left _ (by norm_num)]; push_cast; ring
  · rw [pow_add, pow_mul, neg_one_sq, one_pow, show (2 * k + 1) / 2 = k by omega]; push_cast; ring

lemma Tq_eq (p a : ℕ) : Tq p a = ((p - 1 : ℕ) : ℤ) - 2 * ((∑ b ∈ Ico 1 p, a * b / p : ℕ) : ℤ) +
    4 * ((∑ b ∈ Ico 1 p, a * b / (2 * p) : ℕ) : ℤ) := by
  unfold Tq
  have : ∀ b ∈ Ico 1 p, (-1 : ℤ) ^ (a * b / p) =
      1 - 2 * ((a * b / p : ℕ) : ℤ) + 4 * ((a * b / (2 * p) : ℕ) : ℤ) := by
    intro b _; rw [neg_one_pow_eq, Nat.div_div_eq_div_mul, mul_comm p 2]
  rw [sum_congr rfl this, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum]
  push_cast
  simp

lemma Ico_eq_Icc (p : ℕ) (hp : 0 < p) : Ico 1 p = Icc 1 (p - 1) := by
  ext b; simp only [mem_Ico, mem_Icc]; omega

/-- **Lemma 2.5, first part**: `T(a) = (p - 1) a - 4 F(2p, a)` for odd `a < p`. -/
lemma Tq_odd (p a : ℕ) (hp : p.Prime) (hodd : Odd a) (hap : a < p) :
    Tq p a = ((p - 1 : ℕ) : ℤ) * a - 4 * (Ffl (2 * p) a : ℤ) := by
  have hp0 := hp.pos
  have ha1 : 1 ≤ a := hodd.pos
  obtain ⟨k, hk⟩ := hodd
  have hpa : ¬ p ∣ a := fun h => by have := Nat.le_of_dvd (by omega) h; omega
  have hG := sum_floor_ab p a hp hpa
  have hL := lattice a (2 * p) (p - 1) ((a - 1) / 2) (by omega) (by omega)
    (fun b hb => floor_half a b (2 * p) (p - 1) (by omega) (mem_Icc.mp hb).2)
    (fun c hc => by
      have := floor_half (2 * p) c a ((a - 1) / 2) (by omega) (mem_Icc.mp hc).2
      omega)
    (by
      intro b hb c _ he
      have hd : p ∣ a * b := ⟨2 * c, by rw [he]; ring⟩
      rcases (Nat.Prime.dvd_mul hp).mp hd with h | h
      · exact hpa h
      · have := Nat.le_of_dvd (mem_Icc.mp hb).1 h; have := (mem_Icc.mp hb).2; omega)
  rw [← Ico_eq_Icc p hp0] at hL
  have hF : ∑ c ∈ Icc 1 ((a - 1) / 2), 2 * p * c / a = Ffl (2 * p) a := by
    unfold Ffl; exact sum_congr rfl fun c _ => by rw [mul_comm]
  rw [hF] at hL
  have hU : 2 * ((a - 1) / 2) + 1 = a := by omega
  rw [Tq_eq]
  have hG' : (2 * ((∑ b ∈ Ico 1 p, a * b / p : ℕ) : ℤ) + ((p - 1 : ℕ) : ℤ)) =
      (a : ℤ) * ((p - 1 : ℕ) : ℤ) := by exact_mod_cast hG
  have hL' : ((∑ b ∈ Ico 1 p, a * b / (2 * p) : ℕ) : ℤ) + (Ffl (2 * p) a : ℤ) =
      ((p - 1 : ℕ) : ℤ) * (((a - 1) / 2 : ℕ) : ℤ) := by exact_mod_cast hL
  have hU' : 2 * (((a - 1) / 2 : ℕ) : ℤ) + 1 = (a : ℤ) := by exact_mod_cast hU
  linear_combination (-1 : ℤ) * hG' + 4 * hL' + 2 * ((p - 1 : ℕ) : ℤ) * hU'

/-- `T(a) = 0` for even `a < p` (Lemma 2.1(b)). -/
lemma Tq_even (p a : ℕ) (hp : p.Prime) (heven : Even a) (ha1 : 1 ≤ a) (hap : a < p) :
    Tq p a = 0 := by
  obtain ⟨a', ha'⟩ := heven
  have hp0 := hp.pos
  have hpa : ¬ p ∣ a := fun h => by have := Nat.le_of_dvd (by omega) h; omega
  have hpa' : ¬ p ∣ a' := fun h => by have := Nat.le_of_dvd (by omega) h; omega
  have hG := sum_floor_ab p a hp hpa
  have hG2 := sum_floor_ab p a' hp hpa'
  have hH : ∑ b ∈ Ico 1 p, a * b / (2 * p) = ∑ b ∈ Ico 1 p, a' * b / p := by
    refine sum_congr rfl fun b _ => ?_
    rw [show a * b = 2 * (a' * b) by rw [ha']; ring, Nat.mul_div_mul_left _ _ (by norm_num)]
  rw [Tq_eq, hH]
  have hG' : (2 * ((∑ b ∈ Ico 1 p, a * b / p : ℕ) : ℤ) + ((p - 1 : ℕ) : ℤ)) =
      (a : ℤ) * ((p - 1 : ℕ) : ℤ) := by exact_mod_cast hG
  have hG2' : (2 * ((∑ b ∈ Ico 1 p, a' * b / p : ℕ) : ℤ) + ((p - 1 : ℕ) : ℤ)) =
      (a' : ℤ) * ((p - 1 : ℕ) : ℤ) := by exact_mod_cast hG2
  have ha'' : (a : ℤ) = a' + a' := by exact_mod_cast ha'
  linear_combination (-1 : ℤ) * hG' + 2 * hG2' - ((p - 1 : ℕ) : ℤ) * ha''

/-- Lemma 2.1(c): `S'(p - a, p) = T(a)`. -/
lemma S'_reflect (p a : ℕ) (hp : p.Prime) (ha1 : 1 ≤ a) (hap : a < p) :
    S' (p - a) p = Tq p a := by
  rw [S'_eq]; unfold Tq
  refine sum_congr rfl fun j hj => ?_
  simp only [mem_Ico] at hj
  have hp0 := hp.pos
  have hd := div_add_div_succ (a * j) ((p - a) * j) p j hp0
    (by rw [← add_mul, Nat.add_sub_cancel' hap.le, mul_comm])
    (by
      intro hd
      rcases (Nat.Prime.dvd_mul hp).mp hd with h | h
      · have := Nat.le_of_dvd (by omega) h; omega
      · have := Nat.le_of_dvd (by omega) h; omega)
  rw [show j + 1 + (p - a) * j / p = a * j / p + 2 * ((p - a) * j / p + 1) by omega, pow_add,
    pow_mul, neg_one_sq, one_pow, mul_one]

/-- `S(p) = ∑_{a=1}^{p-1} T(a)`. -/
lemma S_eq_sumT (p : ℕ) (hp : p.Prime) : S p = ∑ a ∈ Ico 1 p, Tq p a := by
  unfold S
  apply sum_nbij' (fun h => p - h) (fun a => p - a)
  · intro b hb; simp only [mem_Ico] at hb ⊢; omega
  · intro b hb; simp only [mem_Ico] at hb ⊢; omega
  · intro b hb; simp only [mem_Ico] at hb; omega
  · intro b hb; simp only [mem_Ico] at hb; omega
  · intro h hh
    simp only [mem_Ico] at hh
    rw [← S'_reflect p (p - h) hp (by omega) (by omega), Nat.sub_sub_self hh.2.le]

lemma sum_range_two_mul (g : ℕ → ℤ) (m : ℕ) :
    ∑ i ∈ range (2 * m), g i = ∑ k ∈ range m, (g (2 * k) + g (2 * k + 1)) := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih, sum_range_succ]
    ring

lemma sum_range_odd (m : ℕ) : ∑ k ∈ range m, (2 * (k : ℤ) + 1) = (m : ℤ) ^ 2 := by
  induction m with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

lemma Ffl_one (x : ℕ) : Ffl x 1 = 0 := by simp [Ffl]

lemma S_eq_range (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    S p = ∑ k ∈ range ((p - 1) / 2),
      (((p - 1 : ℕ) : ℤ) * (2 * k + 1 : ℕ) - 4 * (Ffl (2 * p) (2 * k + 1) : ℤ)) := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hp3 := hp.two_le
  obtain ⟨m, hm⟩ := hodd
  rw [S_eq_sumT p hp, sum_Ico_eq_sum_range, show p - 1 = 2 * m by omega, sum_range_two_mul,
    show 2 * m / 2 = m by omega]
  refine sum_congr rfl fun k hk => ?_
  simp only [mem_range] at hk
  rw [Tq_odd p (1 + 2 * k) hp ⟨k, by ring⟩ (by omega),
    Tq_even p (1 + (2 * k + 1)) hp ⟨k + 1, by ring⟩ (by omega) (by omega),
    show 1 + 2 * k = 2 * k + 1 by ring, show p - 1 = 2 * m by omega]
  ring

/-- **Lemma 2.5** (sum over `a = 2i + 3`): for an odd prime `p`,
`S(p) = (p-1)³/4 - 4 ∑_{i < (p-3)/2} F(2p, 2i+3)`. -/
lemma S_eq_lemma25_range (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    S p = (((p - 1) ^ 3 / 4 : ℕ) : ℤ) - 4 * ((∑ i ∈ range ((p - 3) / 2), Ffl (2 * p) (2 * i + 3) : ℕ) : ℤ) := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hp3 := hp.two_le
  obtain ⟨m, hm⟩ := hodd
  have hm1 : 1 ≤ m := by omega
  rw [S_eq_range p hp hp2, sum_sub_distrib, ← mul_sum, ← mul_sum]
  have h1 : ∑ k ∈ range ((p - 1) / 2), ((2 * k + 1 : ℕ) : ℤ) = (m : ℤ) ^ 2 := by
    rw [show (p - 1) / 2 = m by omega, ← sum_range_odd m]; push_cast; rfl
  have h2 : ∑ k ∈ range ((p - 1) / 2), (Ffl (2 * p) (2 * k + 1) : ℤ) =
      ((∑ i ∈ range ((p - 3) / 2), Ffl (2 * p) (2 * i + 3) : ℕ) : ℤ) := by
    rw [show (p - 1) / 2 = (p - 3) / 2 + 1 by omega, sum_range_succ', Ffl_one]
    push_cast
    simp only [add_zero]
    exact sum_congr rfl fun i _ => by ring_nf
  have h3 : ((p - 1) ^ 3 / 4 : ℕ) = 2 * m ^ 3 := by
    rw [show p - 1 = 2 * m by omega, show (2 * m) ^ 3 = 4 * (2 * m ^ 3) by ring,
      Nat.mul_div_cancel_left _ (by norm_num)]
  rw [h1, h2, h3, show p - 1 = 2 * m by omega]
  push_cast; ring

/-- **Lemma 2.5** of the paper: for an odd prime `p`,
`S(p) = (p-1)³/4 - 4 ∑_{a odd, 3 ≤ a ≤ p-2} F(2p, a)`. -/
theorem S_eq_lemma25 (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    S p = (((p - 1) ^ 3 / 4 : ℕ) : ℤ) - 4 * ∑ a ∈ (Icc 3 (p - 2)).filter Odd, (Ffl (2 * p) a : ℤ) := by
  rw [S_eq_lemma25_range p hp hp2]
  congr 2
  push_cast
  symm
  apply sum_nbij' (fun a => (a - 3) / 2) (fun i => 2 * i + 3)
  · intro a ha; simp only [mem_filter, mem_Icc, mem_range] at ha ⊢
    obtain ⟨⟨h1, h2⟩, k, hk⟩ := ha; omega
  · intro i hi; simp only [mem_filter, mem_Icc, mem_range] at hi ⊢
    exact ⟨⟨by omega, by omega⟩, ⟨i + 1, by ring⟩⟩
  · intro a ha; simp only [mem_filter, mem_Icc] at ha
    obtain ⟨⟨h1, h2⟩, k, hk⟩ := ha; omega
  · intro i _; omega
  · intro a ha; simp only [mem_filter, mem_Icc] at ha
    obtain ⟨⟨h1, h2⟩, k, hk⟩ := ha
    rw [show 2 * ((a - 3) / 2) + 3 = a by omega]

/-! ### The fast evaluator

The loops below use `Nat.rec`, `Bool.rec` and the kernel-accelerated `Nat.add`, `Nat.mul`,
`Nat.div`, `Nat.mod`, `Nat.sub`, `Nat.beq`, `Nat.ble`, `Nat.blt` directly, so that
`decide +kernel` evaluates them quickly. -/

/-- Euclid-type evaluation of `F(x, y)` (fuel `n ≥ y`), as in `code/thetasum.c`:
`F(qy + r, y) = q C(U+1, 2) + (U V - F(y, r))`. -/
def Fe (n : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0)
    (fun _ ih x y => Nat.add
      (Nat.mul (Nat.div x y)
        (Nat.div (Nat.mul (Nat.div (Nat.sub y 1) 2) (Nat.succ (Nat.div (Nat.sub y 1) 2))) 2))
      (Bool.rec (Nat.sub (Nat.mul (Nat.div (Nat.sub y 1) 2) (Nat.div (Nat.sub (Nat.mod x y) 1) 2))
        (ih y (Nat.mod x y))) 0 (Nat.beq (Nat.mod x y) 0))) n

lemma Fe_succ (n x y : ℕ) : Fe (n + 1) x y = x / y * ((y - 1) / 2 * ((y - 1) / 2 + 1) / 2) +
    (if x % y = 0 then 0 else (y - 1) / 2 * ((x % y - 1) / 2) - Fe n y (x % y)) := by
  show Nat.add (Nat.mul (Nat.div x y)
        (Nat.div (Nat.mul (Nat.div (Nat.sub y 1) 2) (Nat.succ (Nat.div (Nat.sub y 1) 2))) 2))
      (Bool.rec (Nat.sub (Nat.mul (Nat.div (Nat.sub y 1) 2) (Nat.div (Nat.sub (Nat.mod x y) 1) 2))
        (Fe n y (Nat.mod x y))) 0 (Nat.beq (Nat.mod x y) 0)) = _
  by_cases h : x % y = 0
  · have hb : Nat.beq (Nat.mod x y) 0 = true := by rw [show Nat.mod x y = 0 from h]; rfl
    rw [hb, if_pos h]; rfl
  · have hb : Nat.beq (Nat.mod x y) 0 = false := by
      rw [Bool.eq_false_iff]; intro h'; exact h (Nat.eq_of_beq_eq_true h')
    rw [hb, if_neg h]; rfl

lemma Ffl_zero (y : ℕ) : Ffl 0 y = 0 := by simp [Ffl]

theorem Fe_eq : ∀ n x y : ℕ, Nat.Coprime x y → 1 ≤ y → y ≤ n → Fe n x y = Ffl x y := by
  intro n
  induction n with
  | zero => intro x y _ h1 h2; omega
  | succ n ih =>
    intro x y hco h1 h2
    have hxy := Nat.div_add_mod x y
    have hadd := Ffl_add (x / y) (x % y) y (by omega)
    rw [show x / y * y + x % y = x by rw [mul_comm]; exact hxy] at hadd
    rw [Fe_succ]
    split_ifs with hr
    · rw [hadd, hr, Ffl_zero]
    · have hrl : x % y < y := Nat.mod_lt x (by omega)
      have hco' : Nat.Coprime (x % y) y := by
        unfold Nat.Coprime; rw [← Nat.gcd_rec, Nat.gcd_comm]; exact hco
      have hrec := Ffl_recip (x % y) y (by omega) (by omega) hco'
      rw [ih y (x % y) hco'.symm (by omega) (by omega), hadd]
      generalize Ffl (x % y) y = A at hrec ⊢
      generalize Ffl y (x % y) = B at hrec ⊢
      generalize (y - 1) / 2 * ((x % y - 1) / 2) = C at hrec ⊢
      omega

/-- `∑_{i<k} f i`, by a loop. -/
def rep (f : ℕ → ℕ) (k : ℕ) : ℕ := Nat.rec (motive := fun _ => ℕ) 0 (fun i ih => Nat.add ih (f i)) k

lemma rep_eq (f : ℕ → ℕ) : ∀ k, rep f k = ∑ i ∈ range k, f i := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => show rep f k + f k = _; rw [ih, sum_range_succ]

/-- `∑_{i<n} f i` as a two-level loop (blocks of 64), to keep the kernel's recursion shallow. -/
def rep2 (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.add (rep (fun j => rep (fun t => f (Nat.add (Nat.mul 64 j) t)) 64) (Nat.div n 64))
    (rep (fun t => f (Nat.add (Nat.mul 64 (Nat.div n 64)) t)) (Nat.mod n 64))

lemma rep2_eq (f : ℕ → ℕ) (n : ℕ) : rep2 f n = ∑ i ∈ range n, f i := by
  have hq : ∀ q, ∑ i ∈ range (64 * q), f i = ∑ j ∈ range q, ∑ t ∈ range 64, f (64 * j + t) := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      rw [show 64 * (q + 1) = 64 * q + 64 by ring, sum_range_add, ih,
        sum_range_succ (fun j => ∑ t ∈ range 64, f (64 * j + t)) q]
  show rep _ (n / 64) + rep _ (n % 64) = _
  rw [rep_eq, rep_eq]
  simp only [rep_eq]
  conv_rhs => rw [← Nat.div_add_mod n 64, sum_range_add, hq]
  rfl

/-- `∑_{i<n} F(2p, 2i+3)`, by a loop (fuel `p`). -/
def sumLoop (p n : ℕ) : ℕ := rep2 (fun i => Fe p (Nat.mul 2 p) (Nat.add (Nat.mul 2 i) 3)) n

lemma sumLoop_eq (p : ℕ) (hp : p.Prime) (n : ℕ) (hn : 2 * n + 1 < p) :
    sumLoop p n = ∑ i ∈ range n, Ffl (2 * p) (2 * i + 3) := by
  unfold sumLoop
  rw [rep2_eq]
  refine sum_congr rfl fun i hi => ?_
  simp only [mem_range] at hi
  show Fe p (2 * p) (2 * i + 3) = _
  apply Fe_eq _ _ _ _ (by omega) (by omega)
  refine Nat.coprime_mul_iff_left.mpr ⟨Nat.coprime_two_left.mpr ⟨i + 1, by ring⟩, ?_⟩
  rw [hp.coprime_iff_not_dvd]; intro h; have := Nat.le_of_dvd (by omega) h; omega

/-- The fast evaluator of `S(p)` (Lemma 2.5 with the Euclid-type recursion for `F`). -/
def Sfast (p : ℕ) : ℤ := (((p - 1) ^ 3 / 4 : ℕ) : ℤ) - 4 * (sumLoop p ((p - 3) / 2) : ℤ)

theorem Sfast_eq (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) : Sfast p = S p := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hp3 := hp.two_le
  obtain ⟨m, hm⟩ := hodd
  rw [S_eq_lemma25_range p hp hp2, Sfast, sumLoop_eq p hp _ (by omega)]

/-! ### The kernel-checked computation -/

lemma ble_false {a b : ℕ} (h : b < a) : Nat.ble a b = false := by
  rw [Bool.eq_false_iff]; intro h'; exact absurd (Nat.le_of_ble_eq_true h') (by omega)

/-- The margin required at `p`: `0` for `p ≤ 233`, `2p` for `233 < p ≤ 3119`, `3p` above. -/
def margin (p : ℕ) : ℕ := Bool.rec (Bool.rec (Nat.mul 3 p) (Nat.mul 2 p) (Nat.ble p 3119)) 0 (Nat.ble p 233)

/-- `margin p + 4 s < m`, with `s = ∑ F` and `m = (p-1)³/4` (so `S(p) = m - 4s > margin p`). -/
def condK (p : ℕ) : Bool :=
  Nat.blt (Nat.add (margin p) (Nat.mul 4 (sumLoop p ((p - 3) / 2)))) ((p - 1) ^ 3 / 4)

lemma condK_spec (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (h : condK p = true) :
    0 < S p ∧ (233 < p → 2 * (p : ℤ) < S p) ∧ (3119 < p → 3 * (p : ℤ) < S p) := by
  rw [← Sfast_eq p hp hp2, Sfast]
  have h' : margin p + 4 * sumLoop p ((p - 3) / 2) < (p - 1) ^ 3 / 4 := by
    unfold condK at h; rw [Nat.blt_eq] at h; exact h
  have hm : (p ≤ 233 → margin p = 0) ∧ (233 < p → p ≤ 3119 → margin p = 2 * p) ∧
      (3119 < p → margin p = 3 * p) := by
    unfold margin
    refine ⟨fun h1 => ?_, fun h1 h2 => ?_, fun h1 => ?_⟩
    · rw [Nat.ble_eq_true_of_le h1]
    · rw [ble_false h1, Nat.ble_eq_true_of_le h2]; rfl
    · rw [ble_false (by omega : 233 < p), ble_false h1]; rfl
  generalize sumLoop p ((p - 3) / 2) = s at h'
  generalize (p - 1) ^ 3 / 4 = m at h'
  refine ⟨?_, fun hp' => ?_, fun hp' => ?_⟩
  · have : margin p ≥ 0 := Nat.zero_le _
    omega
  · rcases Nat.lt_or_ge 3119 p with h3 | h3
    · have := hm.2.2 h3; omega
    · have := hm.2.1 hp' h3; omega
  · have := hm.2.2 hp'; omega

/-- Trial division by `d, d+1, …` while `d² ≤ n` (fuel `f`). -/
def noDivK (n f : ℕ) : ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun _ ih d => Bool.rec (Bool.and (Bool.not (Nat.beq (Nat.mod n d) 0)) (ih (Nat.add d 1))) true
      (Nat.blt n (Nat.mul d d))) f

/-- A primality filter that accepts every prime (`trialK_of_prime`). -/
def trialK (n : ℕ) : Bool := Bool.and (Nat.ble 2 n) (noDivK n n 2)

lemma noDivK_of_prime (n : ℕ) (hn : n.Prime) : ∀ f d, 2 ≤ d → noDivK n f d = true := by
  intro f
  induction f with
  | zero => intro d _; rfl
  | succ f ih =>
    intro d hd
    show Bool.rec (Bool.and (Bool.not (Nat.beq (Nat.mod n d) 0)) (noDivK n f (Nat.add d 1))) true
      (Nat.blt n (Nat.mul d d)) = true
    cases hb : Nat.blt n (Nat.mul d d)
    · have hdd : d * d ≤ n := by
        have : ¬ n < d * d := by
          intro h'
          have h'' : Nat.blt n (Nat.mul d d) = true := by rw [Nat.blt_eq]; exact h'
          rw [hb] at h''; exact absurd h'' (by decide)
        omega
      show Bool.and (Bool.not (Nat.beq (Nat.mod n d) 0)) (noDivK n f (Nat.add d 1)) = true
      rw [ih (d + 1) (by omega), Bool.and_true, Bool.not_eq_true']
      rw [Bool.eq_false_iff]
      intro hmod
      have hdvd : d ∣ n := Nat.dvd_of_mod_eq_zero (Nat.eq_of_beq_eq_true hmod)
      have hdn : d < n := by nlinarith
      rcases hn.eq_one_or_self_of_dvd d hdvd with h1 | h1 <;> omega
    · rfl

lemma trialK_of_prime (n : ℕ) (hn : n.Prime) : trialK n = true := by
  unfold trialK
  rw [noDivK_of_prime n hn n 2 le_rfl, Bool.and_true]
  exact Nat.ble_eq_true_of_le hn.two_le

/-- Checks `condK p` for all odd `p ∈ [lo, lo + N)` accepted by `trialK`. -/
def checkK (lo N : ℕ) : Bool :=
  Nat.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun _ ih n => Bool.and
      (Bool.or (Bool.not (Bool.and (Nat.beq (Nat.mod n 2) 1) (trialK n))) (condK n))
      (ih (Nat.add n 1))) N lo

lemma checkK_sound : ∀ N lo, checkK lo N = true →
    ∀ p, lo ≤ p → p < lo + N → p.Prime → p ≠ 2 → condK p = true := by
  intro N
  induction N with
  | zero => intro lo _ p h1 h2; omega
  | succ N ih =>
    intro lo h p h1 h2 hp hp2
    have h' : Bool.and
        (Bool.or (Bool.not (Bool.and (Nat.beq (Nat.mod lo 2) 1) (trialK lo))) (condK lo))
        (checkK (lo + 1) N) = true := h
    rw [Bool.and_eq_true] at h'
    rcases Nat.lt_or_ge lo p with hlt | hge
    · exact ih (lo + 1) h'.2 p (by omega) (by omega) hp hp2
    · have hpl : p = lo := by omega
      subst hpl
      have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
      have h1' := h'.1
      rw [Bool.or_eq_true] at h1'
      rcases h1' with h1' | h1'
      · exfalso
        have hb : Nat.beq (Nat.mod p 2) 1 = true := by rw [show Nat.mod p 2 = 1 from hodd]; rfl
        rw [hb, trialK_of_prime p hp] at h1'
        exact absurd h1' (by decide)
      · exact h1'

lemma checkK_succ (lo N : ℕ) : checkK lo (N + 1) = Bool.and
    (Bool.or (Bool.not (Bool.and (Nat.beq (Nat.mod lo 2) 1) (trialK lo))) (condK lo))
    (checkK (lo + 1) N) := rfl

lemma checkK_append : ∀ N lo M, checkK lo N = true → checkK (lo + N) M = true →
    checkK lo (N + M) = true := by
  intro N
  induction N with
  | zero => intro lo M _ h; simpa using h
  | succ N ih =>
    intro lo M h1 h2
    rw [checkK_succ, Bool.and_eq_true] at h1
    rw [show N + 1 + M = (N + M) + 1 by ring, checkK_succ, Bool.and_eq_true]
    exact ⟨h1.1, ih (lo + 1) M h1.2 (by rwa [show lo + 1 + N = lo + (N + 1) by ring])⟩

end ThetaSum
