import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21946
open PEqualNP.CircuitLowerBounds
def witness : Circuit := ⟨[⟨.and, [1, 2]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [3, 7]⟩, ⟨.or, [3, 5]⟩, ⟨.or, [2, 9]⟩, ⟨.not, [10]⟩, ⟨.and, [0, 11]⟩, ⟨.or, [8, 12]⟩, ⟨.or, [6, 13]⟩], 14⟩
end PEqualNP.Outside.L_meta_21946

open PEqualNP.Outside.L_meta_21946 in
theorem PEqualNP.Outside.L_meta_21946 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33555 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨witness, ?_, by decide, ?_⟩
  ·
    intro g hg
    simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
