import number_theory.arithmetic_function
import algebra.squarefree
import algebra.order.floor
import data.list.intervals
import tactic
import measure_theory.integral.interval_integral
import general
import archive
import defs
import summability
import squarefree_rw
import lemmas_on_asymptotics
import integral_facts

noncomputable theory
open nat finset function filter
open_locale topological_space interval big_operators filter asymptotics arithmetic_function

namespace squarefree_sums

--------------------------------------------
--           THEOREM 2: THE BIG BAD
--------------------------------------------

lemma step0 :
∀ (x : ℕ),
∑ n in finset.Icc 1 x, squarefree_nat n =
∑ n in finset.Icc 1 x, ∑ d in finset.Icc 1 n, ite (d ^ 2 ∣ n) (μ d) 0
:=
begin
  rw squarefree_nat_eq_tμ,
  intros x,
  congr,
  funext n,
  exact rw_tμ,
end

lemma step05 :
∀ (x : ℕ),
∑ n in finset.Icc 1 x, ∑ d in finset.Icc 1 n, ite (d ^ 2 ∣ n) (μ d) 0 =
∑ n in finset.Icc 1 x, ∑ d in finset.Icc 1 x, ite (d ^ 2 ∣ n) (μ d) 0
:=
begin
  intros x,
  apply finset.sum_congr rfl,
  intros y hy,
  apply sum_subset,
  rw subset_iff,
  intros z hz,
  simp at hy,
  simp at hz,
  simp,
  split,
  exact hz.left,
  calc z ≤ y : hz.right ... ≤ x : hy.right,
  intros z hz hz',
  simp at hy,
  simp at hz,
  simp at hz',
  by_cases h : z = 0, simp [h],
  have h' : 1 ≤ z, linarith,
  have h'' : ¬ (z ^ 2 ∣ y), {
    apply nat.not_dvd_of_pos_of_lt (calc 0 < 1 : by linarith ... ≤ y : hy.left),
    rw pow_two,
    have : y = 1 * y, simp,
    rw this,
    exact mul_lt_mul' h' (hz' h') (by simp) (by linarith),
  },
  simp [h''],
end

def num_divides_upto (d : ℕ) (n : ℕ) := ((finset.Icc 1 n).filter (has_dvd.dvd d)).card

-- Swap the order of summation (the really key point)
lemma step1 :
∀ (x : ℕ),
(∑ n in finset.Icc 1 x, ∑ d in finset.Icc 1 x, ite (d ^ 2 ∣ n) (μ d) 0) =
(∑ d in finset.Icc 1 x, ((μ d) * ((finset.Icc 1 x).filter (has_dvd.dvd (d ^ 2))).card))
:=
begin
  intros x,
  have : ∀ (y : ℕ) (s : finset ℕ), ↑(∑ a in s, 1) * (μ y) = ∑ a in s, (μ y), {
    simp,
  },
  conv {
    to_rhs,
    congr,
    skip,
    funext,
    rw card_eq_sum_ones,
    rw mul_comm,
    rw this,
  },
  rw finset.sum_comm,
  congr,
  funext,
  rw sum_ite,
  simp,
end

-- Rewrite inner sum term as floor ( x / d^2 )
lemma Icc_neighbor {a b c : ℕ} (hab : a ≤ b) (hbc : b + 1 ≤ c) :
  finset.Icc a c = finset.Icc a b ∪ finset.Icc (b + 1) c ∧
  disjoint (finset.Icc a b) (finset.Icc (b + 1) c) :=
begin
  split,
  ext x,
  split,
  simp,
  intros hax hxc,
  simp [hax, hxc],
  by_contradiction H,
  push_neg at H,
  linarith [H],
  simp,
  intros h,
  cases h,
  simp [h.left, h.right],
  linarith,
  simp [h.left, h.right],
  linarith,
  rw disjoint_iff_ne,
  simp,
  intros x hax hxb y hby hyc,
  by_contradiction H,
  rw ← H at hby,
  linarith,
end

lemma num_divides_upto_eq (d n : ℕ) : ((finset.Icc 1 n).filter (has_dvd.dvd d)).card = n.div d :=
begin
  induction n with n hn,
  dec_trivial,
  by_cases hh : n = 0,
  simp [hh],
  by_cases hd : d = 0,
  simp [hd],
  dec_trivial,
  by_cases hd' : d = 1,
  simp [hd'],
  dec_trivial,
  have : 2 ≤ d, exact two_le_nat_iff_not_zero_one.mpr ⟨hd, hd'⟩,
  have : (1 : ℕ).div d = (1 : ℕ) / d, exact rfl,
  rw this,
  have : (1 : ℕ) / d = 0, exact nat.div_eq_zero (by linarith [this]),
  rw this,
  rw card_eq_zero,
  rw eq_empty_iff_forall_not_mem,
  intros x,
  by_contradiction H,
  rw mem_filter at H,
  simp at H,
  rcases H with ⟨aa, bb⟩,
  rw aa at bb,
  have : d = 1, exact nat.dvd_one.mp bb,
  exact hd' this,

  have aaa : 1 ≤ n, exact one_le_iff_ne_zero.mpr hh,
  have bbb : n + 1 ≤ n + 1, linarith,
  have ccc : n.succ = n + 1, exact rfl,

  obtain ⟨is_union, is_disjoint⟩ := Icc_neighbor aaa bbb,
  rw ccc,
  rw is_union,
  rw filter_union,
  rw card_disjoint_union (disjoint_filter_filter is_disjoint),
  rw hn,
  simp,
  have dvd_case : d ∣ n.succ → (finset.filter (has_dvd.dvd d) {n.succ}).card = 1, {
    intros hd,
    rw card_eq_one,
    use n.succ,
    rw finset.eq_singleton_iff_unique_mem,
    split,
    rw finset.mem_filter,
    simp [hd],
    intros x,
    rw finset.mem_filter,
    rintros ⟨hx, hxx⟩,
    exact finset.mem_singleton.mp hx,
  },
  have not_dvd_case : ¬ (d ∣ n.succ) → (finset.filter (has_dvd.dvd d) {n.succ}).card = 0, {
    intros hd,
    rw card_eq_zero,
    rw finset.eq_empty_iff_forall_not_mem,
    intros x,
    rw finset.mem_filter,
    push_neg,
    intros hx,
    rw finset.mem_singleton at hx,
    rwa ← hx at hd,
  },
  by_cases d ∣ n.succ,
  {
    rw dvd_case h,
    have : n.succ.div d = (n + 1) / d, exact rfl,
    rw this,
    rw succ_div,
    have : n.div d = n / d, exact rfl,
    rw this,
    have : n.succ = n + 1, exact rfl,
    rw this at h,
    simp [h],
  },
  {
    rw not_dvd_case h,
    have : n.succ.div d = (n + 1) / d, exact rfl,
    rw this,
    rw succ_div,
    have : n.div d = n / d, exact rfl,
    rw this,
    have : n.succ = n + 1, exact rfl,
    rw this at h,
    simp [h],
  },
end

lemma step2 :
∀ (x : ℕ),
(∑ d in finset.Icc 1 x, ((μ d) * ((finset.Icc 1 x).filter (has_dvd.dvd (d ^ 2))).card)) =
(∑ d in finset.Icc 1 x, ((μ d) * x.div (d^2)))
:=
begin
  intros x,
  apply finset.sum_congr,
  simp,
  intros y hy,
  rw num_divides_upto_eq,
end

-- Shorten the sum
lemma sqrt_magnitude {n : ℕ} : 2 ≤ n → 1 ≤ sqrt n ∧ (sqrt n + 1) ≤ n :=
begin
  intros hn,
  split,
  linarith [sqrt_pos.mpr (calc 0 < 2 : by linarith ... ≤ n : hn)],
  linarith [sqrt_lt_self (calc 1 < 2 : by linarith ... ≤ n : hn)],
end

lemma step3 :
∀ (x : ℕ),
(∑ d in finset.Icc 1 x, ((μ d) * x.div (d^2))) =
(∑ d in finset.Icc 1 (sqrt x), ((μ d) * x.div (d^2)))
:=
begin
  intros x,
  by_cases x0 : x = 0,
  rw x0,
  simp,
  by_cases x1 : x = 1,
  rw x1,
  rw sqrt_one_eq_one,
  have x2 : 2 ≤ x, exact two_le_nat_iff_not_zero_one.mpr ⟨x0, x1⟩,
  have : 1 ≤ sqrt x ∧ (sqrt x + 1) ≤ x, exact sqrt_magnitude x2,
  obtain ⟨fs_union, fs_disjoint⟩ := Icc_neighbor this.left this.right,
  rw fs_union,
  rw finset.sum_union fs_disjoint,
  simp,
  apply sum_eq_zero,
  intros y hy,
  have : x.div (y ^ 2) = x / (y ^ 2), exact rfl,
  rw this,
  simp,
  right,
  rw int.div_eq_zero_of_lt,
  linarith,
  simp at hy,
  have aaa : x < ((sqrt x) + 1) ^ 2, exact nat.lt_succ_sqrt' x,
  zify at aaa,
  rcases hy with ⟨hyl, hyr⟩,
  have hyl2 : ((sqrt x) + 1) ^ 2 ≤ y ^ 2, exact nat.pow_le_pow_of_le_left hyl 2,
  zify at hyl2,
  calc ↑x < (↑(sqrt x) + 1) ^ 2 : aaa
    ... ≤ ↑y ^ 2 : hyl2,
end


-- It's a lot easier to work with Ico's than Icc's because programming
-- But this means we pick up an O(1) term. Prove this is true!
lemma Icc_eq_Ico_union_singleton {a b : ℕ} (hab : a ≤ b) :
finset.Icc a b = finset.Ico a b ∪ {b} ∧ disjoint (finset.Ico a b) {b} :=
begin
  simp,
  ext x,
  simp,
  split,
  rintros ⟨hax, hxb⟩,
  simp [hax, hxb, lt_or_eq_of_le],
  intros h,
  cases h,
  simp [h, le_of_lt],
  simp [hab, h, le_of_eq],
end

lemma quadratic_monotone_eventually
{a b c : ℝ}
(ha : 0 < a)
:
monotone_on (λ x, a * x ^ 2 + b * x + c) (set.Ici (-b / (2 * a)))
:=
begin
  -- This computation is annoyingly difficult
  have two_a_ne_zero : 2 * a ≠ 0, linarith [ha],
  have : 0 = a * 2 * (-b / (2 * a)) + b,
    ring_nf,
    have : (2 * (2 * a)⁻¹ * b * a) = ((2 * a) * (2 * a)⁻¹ * b), ring,
    rw this,
    rw mul_inv_cancel two_a_ne_zero,
    ring,

  have final_ineq : ∀ (x : ℝ), -b / (2 * a) ≤ x → 0 ≤ a * 2 * x + b,
    intros x hx,
    rw this,
    -- Why does add_lt_add_of_lt_of_le not have an equivalent with all lt's replaced by le's?
    apply add_le_add,
    rw mul_le_mul_left,
    exact hx,
    linarith [ha],
    exact rfl.le,

  let f := (polynomial.monomial 2 a) + (polynomial.monomial 1 b) + (polynomial.C c),
  have : (λ x, f.eval x) = (λ (x : ℝ), a * x ^ 2 + b * x + c),
  {
    funext,
    simp,
  },
  rw ← this,
  apply convex.monotone_on_of_deriv_nonneg (convex_Ici (-b / (2 * a))) (polynomial.continuous_on f) (polynomial.differentiable_on f),
  intros x hx,
  have aa : f.derivative = polynomial.monomial 1 (a * 2) + polynomial.C b, {
    simp,
  },
  have bb : deriv (λ (x : ℝ), f.eval x) = (λ (x : ℝ), (f.derivative.eval x)), {
    funext,
    simp,
    ring,
  },
  rw [bb, aa],
  simp,
  simp at hx,
  exact final_ineq x (le_of_lt hx),
end

lemma zero_dumb
{n : ℕ}
(hn : n ≠ 0)
(hn' : n ≤ 1)
:
n = 1 :=
begin
  have : 0 ≤ n, simp,
  have : 0 < n ∨ 0 = n, exact lt_or_eq_of_le this,
  simp [hn.symm] at this,
  have : (0 : ℕ).succ ≤ n, exact succ_le_iff.mpr this,
  linarith,
end

lemma nat_div_sqrt_sqrt_eq_one
{n : ℕ}
:
9 ≤ n → n.div (sqrt n * sqrt n) = 1
:=
begin
  -- In fact, this value for n = 8 is 3 which is the max
  intros hn,
  have one_le_sqrt_n : 1 ≤ sqrt n,  {
    rw ← sqrt_one_eq_one,
    apply sqrt_le_sqrt,
    calc 1 ≤ 9 : by linarith ... ≤ n : hn,
  },

  have zero_lt_sqrt_n : 0 < sqrt n, calc 0 < 1 : by linarith ... ≤ sqrt n : one_le_sqrt_n,
  have le_half : n / (sqrt n * sqrt n) ≠ 0, {
    by_contradiction H,
    rw nat.div_eq_zero_iff at H,
    let bar := calc sqrt n * sqrt n ≤ n : nat.sqrt_le n ... < sqrt n * sqrt n : H,
    linarith,
    simp [zero_lt_sqrt_n],
  },

  have : n ≤ (sqrt n + 1) * (sqrt n + 1), exact le_of_lt (nat.lt_succ_sqrt n),
  have blah : n / (sqrt n * sqrt n) ≤ ((sqrt n + 1) * (sqrt n + 1)) / ((sqrt n) * (sqrt n)), {
    exact nat.div_le_div_right this,
  },
  have : ((sqrt n + 1) * (sqrt n + 1)) = (sqrt n * sqrt n) + 2 * sqrt n + 1, ring,
  rw this at blah,
  have zzz : 2 * sqrt n + 1 < sqrt n * sqrt n,
  {
    let f := (λ (x : ℝ), 1 * x ^ 2 + -2 * x + -1),
    have fequiv : ∀ (x : ℝ), f x = 1 * x ^ 2 + -2 * x + -1, simp,
    have : monotone_on f (set.Ici (- - 2 / (2 * 1))),
      exact quadratic_monotone_eventually (by simp),

    have aa : 3 ≤ sqrt n, {
      have : 9 = 3 * 3, dec_trivial,
      have : sqrt 9 = 3, rw this, exact sqrt_eq 3,
      calc 3 = sqrt 9 : this.symm ... ≤ sqrt n : sqrt_le_sqrt hn,
    },
    have aa' : (3 : ℝ) ≤ ↑(sqrt n), {
      have : (3 : ℝ) = ↑(3 : ℕ), simp,
      rw this,
      exact cast_le.mpr aa,
    },
    have bb : - - (2: ℝ) / (2 * 1) ≤ 3, simp,
    have bb' : (3 : ℝ) ∈ set.Ici (- - (2: ℝ) / (2 * 1)), simp [bb],
    have cc : - - (2 : ℝ) / (2 * 1) ≤ ↑(sqrt n), calc - - (2 : ℝ) / (2 * 1) ≤ (3 : ℝ) : bb ... ≤ ↑(sqrt n) : aa',
    have cc' : ↑(sqrt n) ∈ set.Ici (- - (2: ℝ) / (2 * 1)), simp, linarith,
    unfold monotone_on at this,
    specialize this bb' cc' aa',
    have aa : 0 < f 3, simp,
    linarith,
    zify,
    have bb : f ↑(sqrt n) = ↑(((sqrt n * sqrt n) : ℤ) - 2 * (sqrt n) - 1), {
      rw fequiv,
      norm_cast,
      simp,
      ring,
    },
    have : (0 : ℝ) < ↑(((sqrt n * sqrt n) : ℤ) - 2 * (sqrt n) - 1), linarith,
    norm_cast at this,
    simp at this,
    linarith,
  },
  have : (2 * sqrt n + 1) / (sqrt n * sqrt n) = 0, exact nat.div_eq_zero zzz,
  have : (sqrt n * sqrt n + 2 * sqrt n + 1) / (sqrt n * sqrt n) = (2 * sqrt n + 1) / (sqrt n * sqrt n) + 1,
    apply nat.add_div_left (2 * sqrt n + 1),
    linarith,
  rw nat.div_eq_zero zzz at this,
  rw this at blah,
  simp at blah,

  -- OK, I have that it's ≤ 1 and that it ≠ 0 so why is this so hard :'-(
    exact zero_dumb le_half blah,
end

lemma step35 :
is_Ot
(λ x, (∑ d in finset.Icc 1 (sqrt x), ((μ d) * x.div (d^2))))
(λ x, (∑ d in finset.Ico 1 (sqrt x), ((μ d) * x.div (d^2))))
1
at_top
:=
begin
  unfold is_Ot,
  use 1,
  unfold asymptotics.is_O_with,
  simp,
  use 100,
  intros n hn,
  rw real.norm_eq_abs,
  have : 1 ≤ sqrt n, {rw ← sqrt_one_eq_one, apply sqrt_le_sqrt, calc 1 ≤ 100 : by linarith ... ≤ n : hn, },
  rw (Icc_eq_Ico_union_singleton this).left,
  rw finset.sum_union (Icc_eq_Ico_union_singleton this).right,
  simp,
  rw pow_two,
  have : 9 ≤ n, linarith,
  rw nat_div_sqrt_sqrt_eq_one this,
  simp,
  -- Explicit casts :-(
  conv {
    to_lhs,
    rw ← int.cast_abs,
  },
  rw ← int.cast_one,
  rw int.cast_le,
  exact abs_mu_le_one,
end

lemma first_steps :
∀ (x : ℕ),
∑ n in finset.Icc 1 x, squarefree_nat n =
(∑ d in finset.Icc 1 (sqrt x), ((μ d) * x.div (d^2)))
:=
begin
  intros x,
  transitivity, exact step0 x,
  transitivity, exact step05 x,
  transitivity, exact step1 x,
  transitivity, exact step2 x,
  transitivity, exact step3 x,
  refl,
end

/- The casts will screw us up below -/
lemma first_steps_R :
∀ (x : ℕ),
∑ n in finset.Icc 1 x, ((squarefree_nat n) : ℝ) =
(∑ d in finset.Icc 1 (sqrt x), ((μ d) * x.div (d^2)))
:=
begin
  intros x,
  norm_cast,
  exact first_steps x,
end

lemma first_steps' :
is_Ot
(λ x, (∑ n in finset.Icc 1 x, squarefree_nat n))
(λ x, (∑ d in finset.Ico 1 (sqrt x), ((μ d) * x.div (d^2))))
1
at_top
:=
begin
  conv {
    congr,
    funext,
    rw first_steps_R x,
  },
  exact step35,
end

-- Converting from natural division to real division only picks up √x in error
def μ_over_d2 (d : ℕ) := ↑(μ d) * ((d : ℝ) ^ 2)⁻¹

def sum_μ_times_floor_n_over_d2 (n : ℕ) :=
((∑ d in finset.Ico 1 (sqrt n), (μ d) * n.div (d^2)) : ℝ)

def sum_μ_times_n_over_d2 (n : ℕ) :=
∑ d in finset.Ico 1 (sqrt n), ↑n * μ_over_d2 d -- ↑(μ d) * ↑n * ((d : ℝ) ^ 2)⁻¹

lemma dumbdumb {a b c d : ℝ} : |a * b - c * (a * d)| = |a| * |b - c * d| :=
begin
  ring_nf,
  rw abs_mul,
  conv {
    to_lhs,
    congr,
    congr,
    congr,
    skip,
    rw mul_comm,
  },
end

lemma afaf {a b : ℝ} : |a| ≤ 1 ∧ |b| ≤ 1 → |a| * |b| ≤ 1 :=
begin
  rintros ⟨ha, hb⟩,
  have : (1 : ℝ) = 1 * 1, ring,
  rw this,
  exact mul_le_mul ha hb (abs_nonneg b) (by linarith),
end

lemma step4 :
is_Ot
sum_μ_times_floor_n_over_d2
sum_μ_times_n_over_d2
(λ n, ((sqrt n) : ℝ))
at_top
:=
begin
  unfold is_Ot,
  use 1,
  unfold asymptotics.is_O_with,
  simp,
  use 100,
  intros b hb,
  rw real.norm_eq_abs,
  unfold sum_μ_times_floor_n_over_d2,
  unfold sum_μ_times_n_over_d2,
  rw ← finset.sum_sub_distrib,
  transitivity,
  exact abs_sum_le_sum_abs',
  have u1 : ∀ (d : ℕ), b.div (d ^ 2) = b / (d ^ 2), {
    intros d,
    unfold has_div.div,
  },
  have u2 : ∀ (d : ℕ), (b : ℝ) * (↑d ^ 2)⁻¹ = (b : ℝ) / ↑(d ^ 2), {
    intros d,
    rw div_eq_mul_inv,
    simp,
  },
  unfold μ_over_d2,
  conv {
    to_lhs,
    congr,
    skip,
    funext,
    rw dumbdumb,
    rw u1 x,
    rw u2 x,
    rw abs_sub_comm,
  },
  have u3 : ∀ (d : ℕ), 0 < d → |((μ d) : ℝ)| * |(b : ℝ) / ↑(d ^ 2) - ↑(b / d ^ 2)| ≤ 1,
  {
    intros d hd,
    apply afaf,
    split,
    rw ← int.cast_abs,
    have : (1 : ℝ) = ↑(1 : ℤ), simp,
    rw this,
    rw int.cast_le,
    exact abs_mu_le_one,
    have : 0 < d ^ 2, { rw pow_two, exact (zero_lt_mul_left hd).mpr hd,},
    exact floor_off_by_le_one this,
  },
  have u4 : ∑ (d : ℕ) in finset.Ico 1 (sqrt b), |((μ d) : ℝ)| * |(b : ℝ) / ↑(d ^ 2) - ↑(b / d ^ 2)| ≤ ∑ (d : ℕ) in finset.Ico 1 (sqrt b), 1,
  {
    apply finset.sum_le_sum,
    intros i hi,
    simp at hi,
    exact u3 i (by linarith [hi.left]),
  },
  transitivity,
  exact u4,
  simp,
end



def μ_sum_at_2 := ∑' i, μ_over_d2 i

lemma summable_μ_over_d2 : summable μ_over_d2 :=
begin
  rw ← summable_abs_iff,
  unfold μ_over_d2,
  have u1 : ∀ (i : ℕ), | ((μ i) : ℝ) * (↑i ^ 2)⁻¹| ≤ (↑i ^ 2)⁻¹,
  {
    intros i,
    rw abs_mul,
    by_cases hi : i = 0,
      simp [hi],
    have hi : 0 < i, exact zero_lt_iff.mpr hi,
    have : 0 < ((i : ℝ) ^ 2)⁻¹, simp, norm_cast, apply pow_pos, exact hi,
    rw abs_of_pos this,
    rw mul_comm,
    rw ← le_div_iff' this,
    rw div_self ((ne_of_lt this).symm),
    have : (1 : ℝ) = ↑(1 : ℕ), simp,
    rw this,
    norm_cast,
    exact abs_mu_le_one,
  },
  have u2 : ∀ (i : ℕ), 0 ≤ | ((μ i) : ℝ) * (↑i ^ 2)⁻¹|, intros i, exact abs_nonneg _,
  apply summable_of_nonneg_of_le u2 u1,
  exact one_dirichlet_summable 2 (by simp),
end

def goal_func := (λ (n : ℕ), ↑n * μ_sum_at_2)

def one_over_d2_from (d : ℕ) := (∑' i, ite (d ≤ i) ((i : ℝ) ^ 2)⁻¹ 0)

lemma blarg
{n : ℕ}
{f : ℕ → ℝ}
(hf : f 0 = 0)
:
∑' (i : ℕ), ite (i < n) (f i) 0 = ∑ i in finset.Ico 1 n, f i
:=
begin
  rw head_sum_eq',
  symmetry,
  have : finset.Ico 1 n ⊆ finset.Ico 0 n,
  {
    rw subset_iff,
    intros x,
    simp,
  },
  apply finset.sum_subset this,
  intros x hx hx',
  have : x = 0, {
    simp at hx,
    simp at hx',
    by_contradiction H,
    have : 1 ≤ x, exact nat.one_le_iff_ne_zero.mpr H,
    linarith [calc n ≤ x : hx' this ... < n : hx],
  },
  simp [hf, this],
end

lemma tsum_sub_head_eq_tail''
{n : ℕ}
{f : ℕ → ℝ}
(hf : f 0 = 0)
:
summable f → ∑' (i : ℕ), f i - ∑ (i : ℕ) in finset.Ico 1 n, f i = ∑' (i : ℕ), ite (n ≤ i) (f i) 0
:=
begin
  rw ← blarg hf,
  exact tsum_sub_head_eq_tail_lt,
end

-- Extend the sum to infinity and pick up a O(√x) term
lemma step5' :
is_Ot
sum_μ_times_n_over_d2
goal_func
(λ (n : ℕ), ↑n * one_over_d2_from (sqrt n))
at_top
:=
begin
  unfold is_Ot,
  use 1,
  unfold asymptotics.is_O_with,
  simp,
  use 100,
  intros b hb,
  rw [real.norm_eq_abs, real.norm_eq_abs],
  unfold sum_μ_times_n_over_d2,
  unfold goal_func,
  unfold one_over_d2_from,
  have : |∑ (d : ℕ) in Ico 1 (sqrt b), ↑b * μ_over_d2 d - ↑b * μ_sum_at_2| = ↑b * |∑ (d : ℕ) in Ico 1 (sqrt b), μ_over_d2 d - μ_sum_at_2|,
  {
    rw ← mul_sum,
    rw ← mul_sub,
    rw abs_mul,
    -- Casting sadness
    have : (0 : ℝ) ≤ ↑b, {
      have : (0 : ℝ) = ↑(0 : ℕ), simp,
      rw this,
      norm_cast,
      calc 0 ≤ 100 : by linarith ... ≤ b : hb,
    },
    rw abs_of_nonneg this,
  },
  rw this,
  apply mul_le_mul,
  simp,
  {
    -- The meat of the problem
    rw abs_sub_comm,
    unfold μ_sum_at_2,
    have u1 : μ_over_d2 0 = 0, unfold μ_over_d2, simp,
    conv {
      to_lhs,
      congr,
      rw tsum_sub_head_eq_tail'' u1 summable_μ_over_d2,
    },
    transitivity,
    exact abs_tsum_le_tsum_abs,
    have u4 : ∀ (i : ℕ), 0 ≤ ite (sqrt b ≤ i) ((i : ℝ) ^ 2)⁻¹ 0, {
      intros i,
      by_cases h : sqrt b ≤ i, {
        simp [h],
      },
      {
        simp [h],
      }
    },
    rw abs_of_nonneg (tsum_nonneg u4),
    apply tsum_le_tsum,
    intros c,
    by_cases h : sqrt b ≤ c, {
      simp [h],
      unfold μ_over_d2,
      rw abs_mul,
      have : 0 < ((c : ℝ) ^ 2)⁻¹, simp, norm_cast, apply pow_pos, calc 0 < 1 : by linarith ... ≤ sqrt b : one_le_sqrt (calc 1 ≤ 100 : by linarith ... ≤ b : hb) ... ≤ c : h,
      rw abs_of_pos this,
      rw mul_comm,
      rw ← le_div_iff' this,
      rw div_self ((ne_of_lt this).symm),
      have : (1 : ℝ) = ↑(1 : ℕ), simp,
      rw this,
      norm_cast,
      exact abs_mu_le_one,
    },
    {
      simp [h],
    },
    have : ∀ (c : ℕ), |ite (sqrt b ≤ c) (μ_over_d2 c) 0| = ite (sqrt b ≤ c) (|μ_over_d2 c|) 0, {
      intros c,
      by_cases h : sqrt b ≤ c,
        simp [h],
        simp [h],
    },
    conv {
      congr,
      funext,
      rw this b,
    },
    apply tail_summable',
    rw summable_abs_iff,
    exact summable_μ_over_d2,
    apply tail_summable',
    exact one_dirichlet_summable 2 (by simp),
  },
  exact abs_nonneg _,
  -- This collection of explicit casts is very annoying
  have : (0 : ℝ) = ↑ (0 : ℕ), simp,
  rw this,
  rw nat.cast_le,
  linarith [hb],
end

lemma step6 :
asymptotics.is_O
(λ (n : ℕ), ↑n * one_over_d2_from (sqrt n))
(λ (n : ℕ), (n : ℝ) ^ ((1 : ℝ) / 2))
at_top
:=
begin
  unfold asymptotics.is_O,
  use 2,
  unfold asymptotics.is_O_with,
  simp,
  use 200,
  intros b hb,
  rw [real.norm_eq_abs, real.norm_eq_abs],
  rw ← le_div_iff' (calc (0 : ℝ) < ↑(200 : ℕ) : by {simp, linarith, } ... ≤ ↑b : cast_le.mpr hb),
  unfold one_over_d2_from,
  transitivity,
  exact abs_tsum_le_tsum_abs,

  have : ∑' (i : ℕ), |ite (sqrt b ≤ i) ((i : ℝ) ^ 2)⁻¹ 0| = ∑' (i : ℕ), ite (sqrt b ≤ i) ((i : ℝ) ^ 2)⁻¹ 0,
    congr, funext, simp, by_cases sqrt b ≤ i, simp [h], simp [h],
  rw this,

  obtain ⟨c, hc, hc_zero⟩ : ∃ (c : ℕ), sqrt b = c + 1 ∧ 0 < c, exact asdfasdf hb,
  rw hc,
  have hc_cast' : (0 : ℝ) < ↑c, simp [hc_zero],
  have hc_cast : (0 : ℝ) ≤ ↑c, exact le_of_lt hc_cast',
  have : - ↑c ^ (-(2 : ℝ) + 1) / (-(2 : ℝ) + 1) ≤ 2 * |(b : ℝ) ^ (2 : ℝ)⁻¹| / ↑b, exact extraordinarily_annoying hb hc,
  rw ← ge_iff_le,
  transitivity,
  exact this,
  rw ge_iff_le,
  refine @tail_sum_le_tail_integral _ _ (λ (x : ℝ), (x ^ 2)⁻¹) _ _ _,
  have : (λ (b : ℕ), ∫ (x : ℝ) in ↑c..↑b, (λ (x : ℝ), (x ^ 2)⁻¹) x) = (λ (b : ℕ), (λ (b' : ℝ), ∫ (x : ℝ) in ↑c..b', (λ (x : ℝ), (x ^ (-2 : ℝ))) x) ↑b), {
    funext d,
    simp,
    apply interval_integral.integral_congr,
    unfold set.eq_on,
    intros x hx,
    rw real.rpow_neg,
    norm_cast,
    by_cases h : c ≤ d,
      rw interval_eq_Icc (cast_le.mpr h) at hx,
      simp at hx,
      calc (0 : ℝ) = ↑(0 : ℕ) : by simp ... ≤ ↑c : cast_le.mpr (zero_le c) ... ≤ x : hx.left,

      push_neg at h,
      rw interval_eq_Icc' (cast_le.mpr (le_of_lt h)) at hx,
      simp at hx,
      calc (0 : ℝ) = ↑(0 : ℕ) : by simp ... ≤ ↑d : cast_le.mpr (zero_le d) ... ≤ x : hx.left,
  },
  rw this,
  apply (hf.comp tendsto_coe_nat_at_top_at_top),
  exact goal ↑c (-2) hc_cast' (by linarith),
  {
    unfold antitone_on,
    intros a ha b hb hab,

    have b_cast: (b ^ (2 : ℕ)) = (b ^ (2 : ℝ)), norm_cast,
    rw b_cast,
    have a_cast: (a ^ (2 : ℕ)) = (a ^ (2 : ℝ)), norm_cast,
    rw a_cast,
    rw inv_le_inv,
    apply real.rpow_le_rpow,
    simp at ha,
    calc (0 : ℝ) ≤ ↑c : hc_cast ... ≤ a : ha,
    exact hab,
    linarith,

    rw ← b_cast,
    apply pow_pos,
    simp at hb,
    calc (0 : ℝ) < ↑c : hc_cast' ... ≤ b : hb,

    rw ← a_cast,
    apply pow_pos,
    simp at ha,
    calc (0 : ℝ) < ↑c : hc_cast' ... ≤ a : ha,
  },
  {
    intros a ha,
    simp,
    apply pow_nonneg,
    simp at ha,
    calc (0 : ℝ) ≤ ↑c : hc_cast ... ≤ a : ha,
  },
end

lemma step45 :
asymptotics.is_O
(λ (n : ℕ), ((sqrt n) : ℝ))
(λ (n : ℕ), (n : ℝ) ^ ((1 : ℝ) / 2))
at_top
:=
begin
  unfold asymptotics.is_O,
  use 1,
  unfold asymptotics.is_O_with,
  simp,
  use 1,
  intros b hb,
  rw real.norm_eq_abs,
  rw mul_self_le_mul_self_iff _ _,
  rw ← abs_mul,
  simp,
  rw ← real.rpow_add,
  have : (2 : ℝ)⁻¹ + 2⁻¹ = 1, ring,
  rw this,
  simp,
  norm_cast,
  exact sqrt_le b,
  norm_cast,
  linarith,
  norm_cast,
  simp,
  exact abs_nonneg _,
end


/- Putting all the steps together -/
theorem bigbad :
is_Ot
(λ (n : ℕ), ∑ (i : ℕ) in finset.Icc 1 n, squarefree_nat i)
goal_func
(λ (n : ℕ), (n : ℝ) ^ ((1 : ℝ) / 2))
at_top
:=
begin
  refine is_Ot_trans_bigger_error_right _ step5' step6,
  refine is_Ot_bigger_error _ step45,
  refine is_Ot_trans_same_error _ step4,
  refine is_Ot_trans_bigger_error_right _ first_steps' _,
  apply is_Ot.congr,
  simp,
  unfold asymptotics.is_O,
  use 1,
  unfold asymptotics.is_O_with,
  rw eventually_iff,
  simp,
  use 1,
  intros b hb,
  exact one_le_sqrt hb,
end

end squarefree_sums