import number_theory.arithmetic_function
import algebra.squarefree
import algebra.order.floor
import data.list.intervals
import tactic
import measure_theory.integral.interval_integral

noncomputable theory
open nat finset function filter
open_locale classical topological_space interval big_operators filter asymptotics arithmetic_function


namespace mything

lemma two_add {n : ℕ} (hn : 2 ≤ n) : ∃ n', n = 2 + n' :=
begin
  have : n - 2 + 2 = n, apply nat.sub_add_cancel hn,
  use n - 2,
  ring_nf,
  exact this.symm,
end

end mything