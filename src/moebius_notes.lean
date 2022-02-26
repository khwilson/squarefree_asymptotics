import number_theory.arithmetic_function
import algebra.squarefree
import algebra.order.floor
import data.list.intervals
import tactic
import measure_theory.integral.interval_integral
import general
import defs

noncomputable theory
open nat finset function filter
open_locale classical topological_space interval big_operators filter asymptotics arithmetic_function

/-
The purpose of this file is to prove that μ^2 n = ∑ d^2 ∣ n, μ d. The basic outline
is to show:
  * μ^2 n = ite (squarefree n) 1 0
  * μ^2 is multiplicative
  * n ↦ ∑ d^2 ∣ n, μ d = (sμ * ζ) n where sμ n = ite (is_square n) (μ sqrt n) 0
  * sμ is multiplicative
  * Thus (sμ * ζ) is multiplicative
  * μ^2 and (sμ * ζ) agree on prime powers, and thus
  * μ^2 = (sμ * ζ)

Along the way there are several lemmas we prove, including that μ is multiplicative
(I couldn't find this in mathlib, strangely).

The file has the following outline:
  * General lemmas. These are lemmas that might exist in mathlib, but I couldn't find them
  * Useful functions. Also some lemmas about specific values of those functions
  * Multiplicative functions are equal if they are equal on prime powers.
    - Surely this is somewhere in mathlib, but I couldn't find it!
  * The various useful functions are multiplicative
  * Writing (sμ * ζ) in an inductive fashion
  * Finishing the proof
-/

namespace squarefree_sums




---------------------------------------------------------------------------------
--       DEALING WITH O MANIPULATION (MIGHT BE IN ASYMPTOTICS PACKAGE ALREADY)
---------------------------------------------------------------------------------

/- Convenience notation for f = g + O(h) -/
-- {E : Type*} [has_norm E] {F : Type*} [has_norm F]
def is_Ot {α : Type*} (f : α → ℝ) (g : α → ℝ) (h : α → ℝ) (l : filter α) : Prop :=
∃ c : ℝ, asymptotics.is_O_with c (f - g) h l

--
theorem is_Ot_transitive {α : Type*} (f : α → ℝ) (g : α → ℝ) (h : α → ℝ) (k : α → ℝ) (l : filter α) :
is_Ot f g h l → is_Ot g k h l → is_Ot f k h l :=
begin
  sorry,
end


--------------------------------------------
--           THEOREM 2: THE BIG BAD
--------------------------------------------

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
  rw ← sqrt_one_eq_one,
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

lemma nat_div_sqrt_sqrt_eq_one
{n : ℕ}
:
9 ≤ n → n.div (sqrt n * sqrt n) = 1
:=
begin
  -- In fact, this value for n = 8 is 3 which is the max
  intros hn,
  have one_le_sqrt_n : 1 ≤ sqrt n,  {
    rw sqrt_one_eq_one,
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
    have bb : f ↑(sqrt n) = ↑((sqrt n * sqrt n) - 2 * (sqrt n) - 1), sorry, -- So much casting nonsense
    have : (0 : ℝ) < ↑((sqrt n * sqrt n) - 2 * (sqrt n) - 1), linarith,
    have : 0 < (sqrt n * sqrt n) - 2 * (sqrt n) - 1, {
      exact cast_lt.mp this,
    },
    sorry,  -- Why is it so damn hard to move things around inequalities even _after_ casts?
  },
  have : (2 * sqrt n + 1) / (sqrt n * sqrt n) = 0, exact nat.div_eq_zero zzz,
  have : (sqrt n * sqrt n + 2 * sqrt n + 1) / (sqrt n * sqrt n) = (2 * sqrt n + 1) / (sqrt n * sqrt n) + 1,
    apply nat.add_div_left (2 * sqrt n + 1),
    linarith,
  rw nat.div_eq_zero zzz at this,
  rw this at blah,
  simp at blah,

  -- OK, I have that it's ≤ 1 and that it ≠ 0 so why is this so hard :'-(
    sorry,
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
  have : 1 ≤ sqrt n, {rw sqrt_one_eq_one, apply sqrt_le_sqrt, calc 1 ≤ 100 : by linarith ... ≤ n : hn, },
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


-- Converting from natural division to real division only picks up √x in error
def μ_over_d2 (d : ℕ) := ↑(μ d) * ((d : ℝ) ^ 2)⁻¹

def sum_μ_times_floor_n_over_d2 (n : ℕ) :=
((∑ d in finset.Ico 1 (sqrt n), (μ d) * n.div (d^2)) : ℝ)

def sum_μ_times_n_over_d2 (n : ℕ) :=
∑ d in finset.Ico 1 (sqrt n), ↑n * μ_over_d2 d -- ↑(μ d) * ↑n * ((d : ℝ) ^ 2)⁻¹

-- How do I use to_floor_semiring?
instance : floor_semiring ℝ :=
{ floor := λ a, ⌊a⌋.to_nat,
  ceil := λ a, ⌈a⌉.to_nat,
  floor_of_neg := λ a ha, int.to_nat_of_nonpos (int.floor_nonpos ha.le),
  gc_floor := λ a n ha, by { rw [int.le_to_nat_iff (int.floor_nonneg.2 ha), int.le_floor], refl },
  gc_ceil := λ a n, by { rw [int.to_nat_le, int.ceil_le], refl } }

lemma floor_off_by_le_one {a b : ℕ} (ha : 0 < a) :
|(b : ℝ) / a - ↑(b / a)| ≤ 1 :=
begin
  by_cases b = 0,
  simp [h],
  have zero_lt_b : 0 < b, exact zero_lt_iff.mpr h,
  by_cases b < a,
  simp [nat.div_eq_zero h],
  rw div_eq_mul_inv,
  have fff: (0 : ℝ) < a, simp [ha],
  have ggg : (0 : ℝ) < a⁻¹, simp [ha],
  have : 0 ≤ (b : ℝ) * (↑a)⁻¹, simp [real.mul_pos, zero_lt_b, ggg],
  rw abs_of_nonneg this,
  rw mul_inv_le_iff fff,
  simp [le_of_lt h],

  rw abs_le,
  let foo := @nat.floor_div_eq_div ℝ (real.linear_ordered_field) (real.floor_semiring) b a,
  rw nat.floor_eq_iff' at foo,
  split,
  linarith [foo.left, foo.right],
  linarith [foo.left, foo.right],
  push_neg at h,
  linarith [nat.div_pos h (by linarith)],
end

lemma dumbdumb {a b c d : ℝ} : |a * b - a * c * d| = |a| * |b - c * d| := by sorry

lemma afaf {a b : ℝ} : |a| ≤ 1 ∧ |b| ≤ 1 → |a| * |b| ≤ 1 :=
begin
  sorry,
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
  conv {to_lhs, congr, skip, funext, rw dumbdumb, rw u1 d, rw u2 d, rw abs_sub_comm,},
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

lemma summable_μ_over_d2 : summable μ_over_d2 := by sorry

def goal_func := (λ (n : ℕ), ↑n * μ_sum_at_2)

def one_over_d2_from (d : ℕ) := (∑' i, ite (d ≤ i) ((i : ℝ) ^ 2)⁻¹ 0)

lemma tsum_sub_head_eq_tail
{n : ℕ}
{f : ℕ → ℝ}
:
summable f → ∑' (i : ℕ), f i - ∑' (i : ℕ), ite (i ≤ n) (f i) 0 = ∑' (i : ℕ), ite (n < i) (f i) 0
:= by sorry

lemma tsum_sub_head_eq_tail'
{n : ℕ}
{f : ℕ → ℝ}
:
summable f → ∑' (i : ℕ), f i - ∑' (i : ℕ), ite (i < n) (f i) 0 = ∑' (i : ℕ), ite (n ≤ i) (f i) 0
:=
begin
  intros hf,
  induction n with n hn,
  simp,
  have : ∀ (i n : ℕ), ite (i < n.succ) (f i) 0 = ite (i ≤ n) (f i) 0,
  {
    intros i n,
    by_cases h : i < n.succ,
    simp [h],
    rw lt_succ_iff at h,
    simp [h],
    simp [h],
    push_neg at h,
    rw succ_le_iff at h,
    rw lt_iff_not_ge' at h,
    simp [h],
  },
  conv {
    to_lhs,
    congr,
    skip,
    congr,
    funext,
    rw this i n,
  },
  rw tsum_sub_head_eq_tail hf,
  have : ∀ (i n : ℕ), ite (n.succ ≤ i) (f i) 0 = ite (n < i) (f i) 0,
  {
    intros i n,
    by_cases h : n.succ ≤ i,
    simp [h],
    rw succ_le_iff at h,
    simp [h],
    simp [h],
    push_neg at h,
    rw lt_succ_iff at h,
    have : ¬ n < i, exact not_lt.mpr h,
    simp [this],
  },
  conv {
    to_rhs,
    congr,
    funext,
    rw this i n,
  },
end

lemma blarg
{n : ℕ}
{f : ℕ → ℝ}
(hf : f 0 = 0)
:
∑' (i : ℕ), ite (i < n) (f i) 0 = ∑ i in finset.Ico 1 n, f i
:=
begin
  sorry,
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
  exact tsum_sub_head_eq_tail',
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
  have : |∑ (d : ℕ) in Ico 1 (sqrt b), ↑b * μ_over_d2 d - ↑b * μ_sum_at_2| = ↑b * |∑ (d : ℕ) in Ico 1 (sqrt b), μ_over_d2 d - μ_sum_at_2|, sorry,
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
    exact abs_tsum_le_tsum_abs _,
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
      sorry,
    },
    {
      simp [h],
    },
    sorry,
    sorry,
  },
  exact abs_nonneg _,
  -- This collection of explicit casts is very annoying
  have : (0 : ℝ) = ↑ (0 : ℕ), simp,
  rw this,
  rw nat.cast_le,
  linarith [hb],
end


lemma abs_tsum_nonneg_eq_tsum
{f : ℕ → ℝ}
(hf : ∀ (n : ℕ), 0 ≤ f n)
:
|∑' (i : ℕ), f i| = ∑' (i : ℕ), f i
:=
begin
  by_cases h : summable f,
  obtain ⟨c, hc⟩ := h,
  rw has_sum.tsum_eq hc,
  apply abs_of_nonneg,
  exact has_sum_mono has_sum_zero hc hf,
  unfold tsum,
  simp [h],
end

lemma step6 :
asymptotics.is_O
(λ (n : ℕ), ↑n * one_over_d2_from (sqrt n))
(λ (n : ℕ), (n : ℝ) ^ ((1 : ℝ) / 2))
at_top
:=
begin
  unfold asymptotics.is_O,
  use 1,
  unfold asymptotics.is_O_with,
  simp,
  use 200,
  intros b hb,
  rw [real.norm_eq_abs, real.norm_eq_abs],
  have : |∑' (i : ℕ), ite (b < ↑i) ((i : ℝ) ^ 2)⁻¹ 0| ≤ ∑' (i : ℕ), |ite (b < ↑i) ((i : ℝ) ^ 2)⁻¹ 0|,
  exact abs_tsum_le_tsum_abs (λ (i : ℕ), ite (b < ↑i) ((i : ℝ) ^ 2)⁻¹ 0),
  have : ∑' (i : ℕ), |ite (b < ↑i) ((i : ℝ) ^ 2)⁻¹ 0| = ∑' (i : ℕ), ite (b < ↑i) ((i : ℝ) ^ 2)⁻¹ 0,
  congr,
  funext,
  simp,
  by_cases b < i,
  simp [h],
  simp [h],
  sorry,
end

theorem bigbad :
is_Ot
(λ (n : ℕ), ∑ (i : ℕ) in finset.Icc 1 n, squarefree_nat i)
goal_func
(λ (n : ℕ), (n : ℝ) ^ ((1 : ℝ) / 2))
at_top
:=
begin

end

end squarefree_sums