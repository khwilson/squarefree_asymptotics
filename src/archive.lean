import analysis.p_series
import number_theory.arithmetic_function
import algebra.squarefree
import algebra.order.field
import data.list.intervals
import data.real.sqrt
import tactic
import measure_theory.integral.interval_integral
import analysis.special_functions.integrals
import general

noncomputable theory
-- open_locale classical
open nat finset list finsupp set function filter measure_theory
open_locale topological_space interval big_operators filter ennreal asymptotics

namespace squarefree_sums

lemma fff
{a : ℕ}
:
(2 : ℝ)⁻¹ * real.sqrt ↑a ≤ (2 : ℝ)⁻¹ * (sqrt a + 1) :=
begin
  have : 0 ≤ real.sqrt ↑a,
  {
    rw real.le_sqrt,
    simp, simp,
  },
  exact mul_le_mul (by simp) real_sqrt_le_nat_sqrt_succ this (by simp),
end

lemma ffff
{c : ℕ}
:
(2 : ℝ)⁻¹ * (↑c + 1 + 1) = (2 : ℝ)⁻¹ * ↑c + 1 :=
begin
  ring,
end

lemma huu
{a b c : ℝ}
(ha : a ≠ 0)
:
a * b = a * c ↔ b = c
:=
begin
  exact mul_right_inj' ha,
end

lemma ffa
{c : ℕ}
(hc : 2 ≤ c)
:
(2 : ℝ)⁻¹ * ↑c + 1 ≤ ↑c ↔ (c : ℝ) + 1 ≤ 2 * ↑c :=
begin
  split,
  intros h,
  norm_cast,
  linarith [hc],
  have bb' : c + 1 ≤ 2 * c, {
    linarith,
  },

  intros h,
  have : (2 : ℝ)⁻¹ * ↑c + 1 = (2 : ℝ)⁻¹ * (↑c + 2), ring,
  rw this,
  rw inv_mul_le_iff,
  norm_cast,
  linarith,
  linarith,
end

lemma ffb
{b c : ℕ}
(hb : 200 ≤ b)
(hbc : sqrt b = c + 1)
:
2 ≤ c :=
begin
  have : 14 = sqrt 200, {
    rw nat.eq_sqrt,
    split,
    linarith,
    linarith,
  },
  have : sqrt 200 ≤ sqrt b, exact nat.sqrt_le_sqrt hb,
  linarith,
end

lemma extraordinarily_annoying
{b c : ℕ}
(hb : 200 ≤ b)
(hbc : sqrt b = c + 1)
:
- ↑c ^ (-(2 : ℝ) + 1) / (-(2 : ℝ) + 1) ≤ 2 * |(b : ℝ) ^ (2 : ℝ)⁻¹| / ↑b
:=
begin
  have hc : 2 ≤ c, exact ffb hb hbc,
  have blah : ((-(1 : ℝ)) / 2) = -(((1 : ℝ)) / 2), {
    simp,
    ring,
  },
  have : (-(2 : ℝ) + 1) = -1, ring,
  have fooblah : (2 : ℝ)⁻¹ = (1 : ℝ) / 2, simp,
  ring_nf,
  rw this,
  rw abs_of_nonneg,
  have : 2 * (b : ℝ)⁻¹ * ↑b ^ (2 : ℝ)⁻¹ = 2 * (b : ℝ) ^ (-(1 : ℝ) / 2), {
    rw ← real.rpow_neg_one,
    rw blah,
    rw fooblah,
    rw mul_assoc,
    rw ← real.rpow_add,
    ring_nf,
    norm_cast,
    linarith [hb],
  },
  rw this,
  rw ← inv_le_inv,
  rw real.rpow_neg,
  simp,
  have : (2 * (b : ℝ) ^ ((-(1 : ℝ)) / 2))⁻¹ = (2 : ℝ)⁻¹ * b ^ ((1 : ℝ) / 2), {
    rw mul_inv₀,
    have : (2 : ℝ)⁻¹ ≠ 0, simp,
    rw mul_right_inj' this,
    rw ← real.rpow_neg,
    ring_nf,
    norm_cast,
    linarith [hb],
  },
  rw this,
  rw ← real.sqrt_eq_rpow,
  transitivity,
  exact fff,
  rw hbc,
  simp,
  rw ffff,
  rw ffa hc,
  norm_cast,
  linarith,
  norm_cast,
  calc 0 ≤ 2 : by linarith ... ≤ c : hc,
  apply mul_pos,
  linarith,
  rw blah,
  rw real.rpow_neg,
  rw inv_pos,
  rw ← real.sqrt_eq_rpow,
  rw lt_iff_le_and_ne,
  split,
  rw real.le_sqrt,
  simp,
  norm_cast,
  linarith [hb],
  symmetry,
  by_contradiction H,
  rw real.sqrt_eq_zero' at H,
  norm_cast at H,
  linarith [hb, H],
  norm_cast,
  linarith [hb],
  rw real.rpow_neg,
  rw inv_pos,
  norm_cast,
  linarith [hc],
  norm_cast,
  linarith [hc],
  rw fooblah,
  rw ← real.sqrt_eq_rpow,
  rw real.le_sqrt,
  simp,
  norm_cast,
  simp,
end

lemma asdfasdf
{b : ℕ}
(hb : 200 ≤ b) :
∃ (c : ℕ), sqrt b = c + 1 ∧ 0 < c :=
begin
  have sqrt200 : 14 = sqrt 200, {
    rw nat.eq_sqrt,
    split,
    linarith,
    linarith,
  },
  have : sqrt 200 ≤ sqrt b, exact nat.sqrt_le_sqrt hb,
  use (sqrt b).pred,
  split,
  rw add_one,
  exact (nat.succ_pred_eq_of_pos (calc 0 < 14 : by linarith ... = sqrt 200 : sqrt200 ... ≤ sqrt b : this)).symm,
  calc 0 < 13 : by linarith ... = (14 : ℕ).pred : by simp ... = (sqrt 200).pred : congr_arg pred sqrt200 ... ≤ (sqrt b).pred : pred_le_pred this,
end

end squarefree_sums
