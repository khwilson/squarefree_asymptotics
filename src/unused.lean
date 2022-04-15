import analysis.p_series
import number_theory.arithmetic_function
import algebra.squarefree
import data.list.intervals
import tactic
import measure_theory.integral.interval_integral
import analysis.special_functions.integrals

noncomputable theory
open nat finset list finsupp set function filter measure_theory
open_locale topological_space interval big_operators filter ennreal asymptotics

------ These are unused in the proof but may be useful to include in mathlib
lemma ceil_succ_mem_Icc_of_mem_Ico {R : Type*} [linear_ordered_semiring R] [floor_semiring R]
  {a b : ℕ} {x : R} (hx : x ∈ set.Ico (a : R) ↑b) :
  (⌊x⌋₊ : R) + 1 ∈ set.Icc (a : R) ↑b :=
begin
  rw set.mem_Ico at hx,
  rw set.mem_Icc,
  norm_cast,
  have zero_le_x := le_trans (nat.cast_le.mpr $ zero_le a) hx.left,
  split,
  { exact le_trans ((nat.le_floor_iff zero_le_x).mpr hx.left) (le_succ ⌊x⌋₊), },
  { have := calc ↑⌊x⌋₊ ≤ x : floor_le zero_le_x ... < b : hx.right,
    norm_cast at this,
    exact lt_iff_add_one_le.mp this, },
end

lemma ceil_succ_mem_Icc_of_mem_Ioo {R : Type*} [linear_ordered_semiring R] [floor_semiring R]
  {a b : ℕ} {x : R} (hx : x ∈ set.Ioo (a : R) ↑b) :
  (⌊x⌋₊ : R) + 1 ∈ set.Icc (a : R) ↑b := ceil_succ_mem_Icc_of_mem_Ico ⟨hx.left.le, hx.right⟩

lemma fooooo {x y : ℝ} {a b : ℕ} {f : ℝ → ℝ}  (hxy : x ≤ y)
  (hf : antitone_on f (set.Icc (a : ℝ) ↑b))
  (hx : x ∈ set.Icc (a : ℝ) ↑b) (hy : y ∈ set.Icc (a : ℝ) ↑b) :
  ite (⌊y⌋₊ + 1 ≤ b) (f ↑(⌊y⌋₊ + 1)) (f ↑b) ≤ ite (⌊x⌋₊ + 1 ≤ b) (f ↑(⌊x⌋₊ + 1)) (f ↑b) :=
begin
  have hx_nonneg : 0 ≤ x, calc (0 : ℝ) ≤ a : cast_nonneg a ... ≤ x : hx.left,
  have hy_nonneg : 0 ≤ y, calc (0 : ℝ) ≤ a : cast_nonneg a ... ≤ y : hy.left,
  by_cases hy' : y = b,
  { simp only [floor_coe, hy', add_le_iff_nonpos_right, _root_.le_zero_iff, nat.one_ne_zero, cast_add, cast_one, if_false],
    by_cases hx' : x = b,
    { simp only [floor_coe, hx', add_le_iff_nonpos_right, _root_.le_zero_iff, nat.one_ne_zero, cast_add, cast_one, if_false], },
    { let foo := lt_of_le_of_ne hx.right hx',
      let bar := succ_le_iff.mpr ((floor_lt hx_nonneg).mpr foo),
      simp only [bar, if_true],
      apply hf,
      { split,
        { calc (a : ℝ) ≤ ⌊x⌋₊ : cast_le.mpr (le_floor hx.left) ... ≤ ⌊x⌋₊ + 1 : by linarith },
        { exact cast_le.mpr bar, }, },
      { exact mem_of_eq_of_mem (eq.symm hy') hy, },
      { norm_cast, exact bar, }, }, },
  { have hy'' : y < b, exact lt_of_le_of_ne hy.right hy',
    have hx'' : x < b, calc x ≤ y : hxy ... < b : hy'',

    have aa : ⌊y⌋₊ + 1 ≤ b, exact succ_le_iff.mpr ((floor_lt hy_nonneg).mpr hy''),
    have cc : ⌊x⌋₊ + 1 ≤ ⌊y⌋₊ + 1, linarith [floor_mono hxy],
    have bb : ⌊x⌋₊ + 1 ≤ b, exact succ_le_iff.mpr ((floor_lt hx_nonneg).mpr hx''),
    simp only [aa, bb, cast_add, cast_one, if_true],
    apply hf,
    { exact ceil_succ_mem_Icc_of_mem_Ico ⟨hx.left, hx''⟩, },
    { exact ceil_succ_mem_Icc_of_mem_Ico ⟨hy.left, hy''⟩, },
    { norm_cast, exact cc, }, },
end


/- Not actually used in proof but a reasonable lemma for showing how to deal with integrals -/
lemma blahblah {a b c d : ℝ} {f : ℝ → ℝ}
  (hf : interval_integrable f real.measure_space.volume a b)
  (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) :
  interval_integrable f real.measure_space.volume c d :=
begin
  rw interval_integrable_iff,
  apply integrable_on.mono_set hf.left,
  rw interval_oc_of_le hcd,
  exact Ioc_subset_Ioc hac hdb,
end
