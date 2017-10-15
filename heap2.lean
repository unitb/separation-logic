import separation.heap
import util.meta.tactic.ite

universes u

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

namespace tactic.interactive

open tactic tactic.interactive (ite_cases)
open lean lean.parser interactive interactive.types

meta def try_then (x y : tactic unit) : tactic unit :=
focus1 $
do (some ()) ← try_core x | tactic.skip,
   tactic.all_goals y

meta def expand_part_ite : tactic unit :=
do tactic.try `[ dsimp [part] ],
   tactic.reflexivity <|> try_then (ite_cases `h) expand_part_ite

meta def break_disjoint_asm_symm (l : expr)
: tactic unit :=
do t ← infer_type l,
   match t with
    | `(%%h₀ ## (%%h₁ : heap)) :=
      do h ← get_unused_name `h,
         to_expr ``(disjoint_symm %%l) >>= note h none,
         return ()
    | _ :=
         fail $ format! "expecting {l} of the form _ ## _"
   end

meta def break_disjoint_asm_r (l : expr)
: tactic (list expr) :=
do t ← infer_type l,
   match t with
    | `(%%h₀ ## part' %%h₁ %%h₂ %%h₃) :=
      do h ← get_unused_name `h,
         r ← to_expr ``(disjoint_of_disjoint_part'_right _ %%l) >>= note h none,
         h ← get_unused_name `h,
         r' ← to_expr ``(disjoint_of_disjoint_part'_left _ %%l) >>= note h none,
         try (tactic.clear l),
         return [r,r']
    | _ :=
         fail $ format! "expecting {l} of the form _ ## _"
   end
meta def break_disjoint_asm_l (l : expr)
: tactic (list expr) :=
do t ← infer_type l,
   match t with
    | `(part' %%h₁ %%h₂ %%h₃ ## %%h₀) :=
      do h ← get_unused_name `h,
         r ← to_expr ``(disjoint_of_part'_disjoint_right _ %%l) >>= note h none,
         h ← get_unused_name `h,
         r' ← to_expr ``(disjoint_of_part'_disjoint_left _ %%l) >>= note h none,
         try (tactic.clear l),
         return [r,r']
    | _ :=
         break_disjoint_asm_r l
   end

meta def break_disjoint_asm'
: expr → tactic unit
| l :=
do xs ← break_disjoint_asm_l l,
   xs.for_each (try ∘ break_disjoint_asm')

meta def break_disjoint_asm (l : parse ident)
: tactic (list expr) :=
do get_local l >>= break_disjoint_asm_l

meta def break_disjoint_asms
: tactic unit :=
do ls ← local_context,
   ls.for_each (try ∘ break_disjoint_asm'),
   ls ← local_context,
   ls.for_each (try ∘ break_disjoint_asm_symm)

meta def contradict_asm
: tactic unit :=
do ls ← local_context,
   ls.any_of (λ e,
     do `(¬ %%t) ← infer_type e | failed ,
         exfalso, tactic.apply e, tactic.clear e)

meta def prove_disjoint'
: tactic unit :=
    assumption
<|> (`[ apply part'_disjoint ] ; assumption )
<|> (`[ apply disjoint_part' ] ; assumption )
<|> failed

meta def prove_disjoint
: tactic unit :=
do contradict_asm,
   break_disjoint_asms,
   prove_disjoint'

end tactic.interactive

lemma part_assoc
  (a b c : option heap)
: part (part a b) c = part a (part b c) :=
begin
  cases a ; cases b ; cases c
  ; expand_part_ite,
   all_goals { prove_disjoint <|> rw part'_assoc },
end

lemma part_comm
  (a b : option heap)
: part a b = part b a :=
sorry

instance : is_associative (option heap) part :=
⟨ part_assoc ⟩
instance : is_commutative (option heap) part :=
⟨ part_comm ⟩

lemma disjoint_of_is_some_part
  {hp₀ hp₁ : heap}
  (h : (part (some hp₀) (some hp₁)).is_some)
: hp₀ ## hp₁ :=
sorry

lemma disjoint_of_part_eq_some
  {hp₀ hp₁ hp₂ : heap}
  (h : some hp₂ = (part (some hp₀) (some hp₁)))
: hp₀ ## hp₁ :=
sorry

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
sorry

lemma is_some_of_is_some_part_left
  {hp₀ : option heap} (hp₁ : option heap)
  (h : (part hp₀ hp₁).is_some)
: hp₀.is_some :=
sorry

@[simp]
lemma some_eq_some_iff (x y : heap)
: some x = some y ↔ x = y :=
sorry

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
sorry

@[simp]
lemma part'_eq_emp (a b : option heap)
: part a b = some heap.emp ↔ a = some heap.emp ∧ b = some heap.emp :=
sorry

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
