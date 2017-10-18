import separation.heap
import util.meta.tactic

universes u

namespace heap

section classical

local attribute [instance] classical.prop_decidable

noncomputable def part  : option heap → option heap → option heap
| (some hp₀) (some hp₁) :=
if h : hp₀ ## hp₁
then some $ part' hp₀ hp₁
else none
| _ _ := none

end classical

@[simp]
lemma some_part'
  (hp₀ hp₁ : heap)
  (h : hp₀ ## hp₁)
: some (part' hp₀ hp₁) = part (some hp₀) (some hp₁) :=
by { simp [part,bind,option.bind,dif_pos, h], }

@[simp]
lemma heap_emp_part
  (hp : heap)
: part (some heap.emp) (some hp) = some hp :=
by simp [part]

@[simp]
lemma part_heap_emp
  (hp : heap)
: part (some hp) (some heap.emp) = some hp :=
by simp [part]

end heap

namespace tactic.interactive

open heap
open tactic tactic.interactive (ite_cases)
open lean lean.parser interactive interactive.types

meta def try_then (x y : tactic unit) : tactic unit :=
focus1 $
do (some ()) ← try_core x | tactic.skip,
   tactic.all_goals y

meta def expand_part_ite : tactic unit :=
do tactic.try `[ dsimp [part] ],
   tactic.reflexivity <|> try_then (ite_cases none $ loc.ns [none]) expand_part_ite

meta def contradict_asm
: tactic unit :=
do ls ← local_context,
   ls.any_of (λ e,
     do `(¬ %%t) ← infer_type e | failed ,
         exfalso, tactic.apply e, tactic.clear e)

end tactic.interactive

namespace heap

lemma part_assoc
  (a b c : option heap)
: part (part a b) c = part a (part b c) :=
begin
  cases a ; cases b ; cases c
  ; expand_part_ite,
   all_goals { {contradict_asm ; prove_disjoint} <|> rw part'_assoc },
end

lemma part_comm
  (a b : option heap)
: part a b = part b a :=
begin
  cases a ; cases b
  ; dsimp [part] ; try { refl }
  ; ite_cases with i
  ; ite_cases with i'
  ; try { contradict_asm, symmetry, assumption },
  rw part'_comm,
end

instance : is_associative (option heap) part :=
⟨ part_assoc ⟩
instance : is_commutative (option heap) part :=
⟨ part_comm ⟩

lemma disjoint_of_is_some_part
  {hp₀ hp₁ : heap}
  (h : (part (some hp₀) (some hp₁)).is_some)
: hp₀ ## hp₁ :=
by { dsimp [part] at h,
     ite_cases with h at h,
     contradiction,
     assumption }

lemma disjoint_of_part_eq_some
  {hp₀ hp₁ hp₂ : heap}
  (h : some hp₂ = (part (some hp₀) (some hp₁)))
: hp₀ ## hp₁ :=
by { apply disjoint_of_is_some_part, rw ← h, exact rfl }

lemma eq_part'_of_some_eq_part
  (hp₀ hp₁ hp : heap)
  (h : some hp = part (some hp₀) (some hp₁))
: hp = part' hp₀ hp₁ (disjoint_of_part_eq_some h) :=
by { apply @option.no_confusion _ _ (some hp) (some _) _ id,
     simp [h], }

lemma is_some_of_is_some_part_right
  (hp₀ : option heap) {hp₁ : option heap}
  (h : (part hp₀ hp₁).is_some)
: hp₁.is_some :=
by { cases hp₀ ; cases hp₁ ; try { contradiction },
     exact rfl }

lemma is_some_of_is_some_part_left
  {hp₀ : option heap} (hp₁ : option heap)
  (h : (part hp₀ hp₁).is_some)
: hp₀.is_some :=
by { cases hp₀ ; cases hp₁ ; try { contradiction },
     exact rfl }

@[simp]
lemma some_eq_some_iff (x y : heap)
: some x = some y ↔ x = y :=
by { split ; intro h, injection h, subst x }

def opt_apl : option heap → pointer → option word
 | (some hp) p := hp p
 | none _ := none

lemma opt_apl_some (hp : heap) (p : pointer)
: opt_apl (some hp) p = hp p :=
rfl

lemma opt_apl_part_maplet (hp : heap) (p : pointer) (v : word)
  (h : maplet p v ## hp)
: (opt_apl (part (some (maplet p v)) (some hp)) p) = some v :=
begin
  unfold part,
  rw [dif_pos] ; [ skip , apply h ],
  rw [opt_apl,part',maplet,if_pos rfl],
  refl,
end

@[simp]
lemma eq_emp_of_part (a : heap) (hp : option heap)
: some a = part (some a) hp ↔ hp = some heap.emp :=
begin
  cases hp ; dsimp [part],
  split ; intro h ; contradiction,
  ite_cases with h₀,
  split ; intros h₁,
  { contradiction },
  { injection h₁ with h₂, simp [h₂] at h₀,
    cases h₀, },
  split ; intro h₁ ; injection h₁ with h₂,
  { simp [eq_emp_of_part'] at h₂,
    simp [h₂] },
  { simp [h₂], }
end

@[simp]
lemma part'_eq_emp (a b : option heap)
: part a b = some heap.emp ↔ a = some heap.emp ∧ b = some heap.emp :=
begin
  split ; simp_intros h ;
  cases a ; cases b
  ; try { refl }
  ; try { cases h with h₀ h₁ }
  ; try { contradiction }
  ; try { rw [h₀,h₁,← some_part' _ _ (disjoint_heap_emp _)
             ,heap_emp_part'_eq_self] },
  { unfold part at h,
    revert h, ite_cases with h,
    contradiction,
    intro h₀,
    injection h₀ with h₁,
    have h₂ : ∀ p, part' a a_1 h p = heap.emp p,
    { intro, rw h₁ },
    simp [part',heap.emp] at h₂,
    split ; congr ; funext p,
    { simp [(h₂ p).left], refl },
    { simp [(h₂ p).right], refl }, }
end

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
  by_cases (p = p') with h,
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
