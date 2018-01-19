import separation.heap.lemmas
import util.meta.tactic

universes u

namespace heap

def heap.le (hp₀ hp₁ : heap) : Prop :=
∃ hp, some hp₁ = part (some hp₀) hp

instance : has_le heap :=
⟨ heap.le ⟩

instance : partial_order heap :=
{ le := heap.le
, le_refl := by { intro x, existsi (some heap.emp), simp, }
, le_trans := by { introv,
                   simp [has_le.le,heap.le],
                   intros hp₀ h₀ hp₁ h₁,
                   -- have : hp₀ ## hp₁, admit,
                   existsi part hp₀ hp₁,
                   simp [h₁,h₀], ac_refl }
, le_antisymm := by { introv,
                      simp [has_le.le,heap.le],
                      intros hp₀ h₀ hp₁ h₁,
                      simp [h₀,part_assoc] at h₁,
                      simp [h₁.left] at h₀,
                      subst b, }
}

lemma part'_delete_maplet (p : pointer) (v : word) (hp : heap)
  (h : heap.delete p 1 hp ## maplet p v)
  (h' : maplet p v ≤ hp)
: part' (heap.delete p 1 hp) (maplet p v) = hp :=
begin
  funext p',
  by_cases h : (p = p'),
  { simp [part', heap.delete, maplet, if_pos, h],
    unfold has_le.le heap.le at h',
    cases h' with hp' h', cases hp' with hp',
    { contradiction },
    have h₂ := eq_part'_of_some_eq_part _ _ _ h',
    rw [h₂,part',maplet,if_pos h],
    simp },
  { simp [part', heap.delete, maplet, if_neg, h] }
end

end heap
