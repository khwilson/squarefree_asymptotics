import number_theory.arithmetic_function
import algebra.squarefree
import algebra.order.floor
import data.list.intervals
import tactic
import measure_theory.integral.interval_integral

noncomputable theory
open nat finset function filter
open_locale topological_space interval big_operators filter asymptotics arithmetic_function

namespace squarefree_sums

def is_square (n : ℕ) : Prop := ∃ s, s * s = n

instance : decidable_pred (is_square : ℕ → Prop)
| n := decidable_of_iff' _ (nat.exists_mul_self n)

def ssqrt (n : ℕ) := ite (is_square n) (sqrt n) 0

def sμ' (d : ℕ) := arithmetic_function.moebius (ssqrt d)
def sμ : arithmetic_function ℤ := ⟨
  sμ',
  by {
    unfold sμ',
    unfold ssqrt,
    simp,
  },
⟩

def tμ := sμ * ζ

def squarefree_nat' (d : ℕ) := ite (squarefree d) (1 : ℤ) (0 : ℤ)

def squarefree_nat : arithmetic_function ℤ :=
⟨
  squarefree_nat',
  (by {
    unfold squarefree_nat',
    have : ¬squarefree 0, exact not_squarefree_zero,
    simp [this],
  }),
⟩

def is_Ot {α : Type*} (f : α → ℝ) (g : α → ℝ) (h : α → ℝ) (l : filter α) : Prop :=
∃ c : ℝ, asymptotics.is_O_with c (f - g) h l

end squarefree_sums