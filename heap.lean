import data.bitvec
import data.dlist
import data.list.perm
import util.logic
import util.control.applicative
import util.control.monad.non_termination
import util.data.option
import util.meta.tactic
import util.meta.tactic.perm

universes u v w w'

open nat list (hiding bind) function

@[reducible]
def pointer := ℕ

structure word :=
to_word :: (to_ptr : ℕ)

instance : has_zero word := ⟨ ⟨ 0 ⟩ ⟩
instance : has_one word := ⟨ ⟨ 1 ⟩ ⟩
instance : has_add word := ⟨ λ x y, ⟨ x.to_ptr + y.to_ptr ⟩ ⟩

def heap := pointer → option word

def disjoint (h₀ h₁ : heap) :=
(∀ p, h₀ p = none ∨ h₁ p = none)

infix ` ## `:51 := disjoint

def part'  (h₀ h₁ : heap) (_ : h₀ ## h₁ . tactic.assumption) : heap
 | p := h₀ p <|> h₁ p

def maplet (p : pointer) (v : word) : heap
  | q :=
if p = q then some v else none

def heap.emp : heap :=
λ _, none

@[simp]
lemma heap_emp_disjoint (h : heap)
: heap.emp ## h :=
by { dunfold disjoint heap.emp, intros, left, refl }

@[simp]
lemma disjoint_heap_emp (h : heap)
: h ## heap.emp :=
by { dunfold disjoint heap.emp, intros, right, refl }

@[simp]
lemma heap_emp_part'_eq_self (h : heap)
: part' heap.emp h (heap_emp_disjoint _) = h :=
begin
  apply funext, intro,
  unfold part',
  cases (h x) ; simp [heap.emp,has_orelse.orelse,option.orelse]
end

@[simp]
lemma part'_heap_emp_eq_self (h : heap)
: part' h heap.emp (disjoint_heap_emp _) = h :=
begin
  apply funext, intro,
  unfold part',
  cases (h x) ; simp [heap.emp,has_orelse.orelse,option.orelse]
end

def heap.mk : pointer → list word → heap
| _ [] := heap.emp
| p (v :: vs) := λ q, maplet p v q <|> heap.mk (p+1) vs q

lemma maplet_disjoint_heap_mk (p : pointer) (v : word) (vs : list word)
: disjoint (maplet p v) (heap.mk (p + 1) vs) :=
sorry

def left_combine (h₀ h₁ : heap) : heap
 | p := h₀ p <|> h₁ p

def heap.delete : pointer → ℕ → heap → heap
 | p 0 h q := h q
 | p (succ n) h q :=
if p = q then none
else heap.delete (p+1) n h q

infix ` <+ `:54 := left_combine

section noncomp

local attribute [instance] classical.prop_decidable

noncomputable def part (h₀ h₁ : heap) : option heap :=
if Hd : h₀ ## h₁
then some (part' h₀ h₁)
else none

end noncomp

@[simp]
lemma heap_emp_part (h : heap)
: part heap.emp h = some h :=
by simp [part]

@[simp]
lemma part_heap_emp (h : heap)
: part h heap.emp = some h :=
by simp [part]

@[symm]
lemma disjoint_symm {h₀ h₁ : heap}
  (h : h₀ ## h₁)
: h₁ ## h₀ :=
assume p, or.symm (h p)

lemma part_comm' {h₀ h₁ : heap}
  (h : h₀ ## h₁)
: part' h₀ h₁ = part' h₁ h₀ (disjoint_symm h) :=
begin
  funext p, unfold part',
  cases h p with h h ; simp [h],
end

lemma part_comm (h₀ h₁ : heap)
: part h₀ h₁ = part h₁ h₀ :=
begin
  unfold part,
  cases classical.em (h₀ ## h₁) with H H,
  { have H' := disjoint_symm H,
    simp [dif_pos,H,H',part_comm' H] },
  { have H' := mt disjoint_symm H,
    simp [dif_neg,H,H'] }
end

lemma disjoint_of_part {h h₀ h₁ : heap}
  (HH : some h = part h₀ h₁)
: h₀ ## h₁ :=
begin
  unfold part at HH,
  apply classical.by_contradiction _,
  intro H,
  rw [dif_neg] at HH,
  { contradiction },
  { assumption }
end

lemma part_disjoint_assoc_left {h₀ h₁ h₂ : heap}
  (Hdisj : h₀ ## h₁)
  (Hdisj' : h₁ ## h₂)
  (h : part' h₀ h₁ Hdisj ## h₂)
: h₀ ## part' h₁ h₂ Hdisj' :=
begin
  intro p,
  cases h p with h' h' ; unfold part' at *,
  { rw or_else_eq_none_iff at h',
    simp [h'.left] },
  { simp [h',Hdisj p], },
end

lemma part_disjoint_assoc_right {h₀ h₁ h₂ : heap}
  (Hdisj : h₀ ## h₁)
  (Hdisj' : h₁ ## h₂)
  (h : h₀ ## part' h₁ h₂)
: part' h₀ h₁ ## h₂ :=
begin
  intro p,
  cases h p with h' h' ; unfold part' at *,
  { simp [h',Hdisj' p], },
  { rw or_else_eq_none_iff at h',
    simp [h'.right] },
end

@[simp]
lemma eq_emp_of_part' (hp a : heap)
  (h  : a ## hp)
: a = part' a hp ↔ hp = heap.emp :=
sorry

@[simp]
lemma eq_emp_of_part (hp a : heap)
: some a = part a hp ↔ hp = heap.emp :=
sorry

@[simp]
lemma part'_eq_emp (a b : heap)
  (h  : a ## b)
: part' a b = heap.emp ↔ a = heap.emp ∧ b = heap.emp :=
sorry

lemma part'_part'_assoc {h₀ h₁ h₂ : heap}
  (Hdisj₀ : h₀ ## h₁)
  (Hdisj₁ : h₁ ## h₂)
  (Hdisj₂ : part' h₀ h₁ ## h₂)
  (Hdisj₃ : h₀ ## part' h₁ h₂)
: part' (part' h₀ h₁) h₂ Hdisj₂ = part' h₀ (part' h₁ h₂) Hdisj₃ :=
sorry

lemma part'_part_assoc {h₀ h₁ h₂ : heap}
  (Hdisj : h₀ ## h₁)
  (Hdisj' : h₁ ## h₂)
: part (part' h₀ h₁) h₂ = part h₀ (part' h₁ h₂) :=
begin
  unfold part,
  cases classical.em (part' h₀ h₁ Hdisj ## h₂) with h h,
  { have h' : (h₀ ## part' h₁ h₂ Hdisj') := part_disjoint_assoc_left _ _ h,
    simp [dif_pos,h,h'],
    apply congr_arg,
    funext p, simp [part',or_else_assoc], },
  { have h' : ¬ (h₀ ## part' h₁ h₂ Hdisj'),
    { rw part_comm',
      apply mt disjoint_symm,
      apply mt (part_disjoint_assoc_left _ _),
      apply mt disjoint_symm,
      rw part_comm',
      apply h,
      apply disjoint_symm Hdisj },
    simp [dif_neg,h,h'] }
end

lemma part'_of_part {h h₀ h₁ : heap}
  (H : some h = part h₀ h₁)
: h = part' h₀ h₁ (disjoint_of_part H) :=
begin
  unfold part at H, dedup,
  simp [dif_pos,disjoint_of_part H] at H_1,
  injection H_1,
end

def heap.le (hp₀ hp₁ : heap) : Prop :=
∃ hp, some hp₁ = part hp₀ hp

instance : has_le heap :=
⟨ heap.le ⟩

instance : partial_order heap :=
{ le := heap.le
, le_refl := by { intro x, existsi heap.emp, simp [part_comm] }
, le_trans := by { introv,
                   simp [has_le.le,heap.le],
                   intros hp₀ h₀ hp₁ h₁,
                   have : hp₀ ## hp₁, admit,
                   existsi part' hp₀ hp₁,
                   rw [h₁,part'_of_part h₀,part'_part_assoc], }
, le_antisymm := by { introv,
                      simp [has_le.le,heap.le],
                      intros hp₀ h₀ hp₁ h₁,
                      have h : hp₀ ## hp₁, admit,
                      rw [part'_of_part h₀,part'_part_assoc _ h
                         ,eq_emp_of_part,part'_eq_emp] at h₁,
                      simp [h₁.left] at h₀,
                      injection h₀, subst b, }
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
    cases h' with hp' h',
    rw [part'_of_part h',part',maplet,if_pos h],
    simp },
  { simp [part', heap.delete, maplet, if_neg, h] }
end

lemma delete_part'_heap_mk {p : pointer} {vs : list word} {hp : heap}
  (h : heap.mk p vs ## hp)
: heap.delete p (length vs) (part' (heap.mk p vs) hp) = hp :=
sorry

lemma disjoint_disjoint_left {h₁ h₂ h₃ : heap}
  (H₁ : h₂ ## h₃)
  (H₀ : part' h₂ h₃ H₁ ## h₁)
: h₁ ## h₃ :=
begin
  intro p,
  cases H₀ p with H₂ H₂,
  { unfold part' at H₂,
    rw or_else_eq_none_iff at H₂,
    simp [H₂.right] },
  { simp [H₂] }
end

lemma disjoint_disjoint_right {h₁ h₂ h₃ : heap}
  (H₁ : h₂ ## h₃)
  (H₀ : part' h₂ h₃ H₁ ## h₁)
: h₁ ## h₂ :=
begin
  have H₁ := disjoint_symm H₁,
  apply disjoint_disjoint_left H₁,
  rw part_comm', apply H₀,
end

noncomputable def parts : list heap → option heap
 | [] := some heap.emp
 | (x :: xs) :=
do ys ← parts xs,
   part x ys

lemma parts_congr {hp₀ hp₁ : list heap}
  (H : hp₀ ~ hp₁)
: parts hp₀ = parts hp₁ :=
begin
  induction H,
  case perm.nil
  { refl },
  case perm.skip
  { unfold parts,
    rw ih_1, },
  case perm.swap
  { unfold parts,
    simp [monad.bind_assoc],
    apply congr_arg,
    funext z,
    unfold part,
    cases classical.em (disjoint x z) with h h
    ; cases classical.em (disjoint y z) with h' h'
    ; simp [h,h']
    ; simp [bind,option.bind],
    { rw [part_comm',← part'_part_assoc h',part_comm], },
    { unfold part,
      rw dif_neg, intros h'', apply h',
      apply disjoint_disjoint_left,
      symmetry, assumption },
    { unfold part,
      rw dif_neg, intros h'', apply h,
      apply disjoint_disjoint_left,
      symmetry, assumption },  },
  case perm.trans
  { cc }
end

lemma part'_eq_parts_app_of_parts_parts {hp₀ hp₁ : heap} {hs₀ hs₁ : list heap}
  (H₀ : hp₀ ## hp₁)
  (H₁ : some hp₀ = parts hs₀)
  (H₂ : some hp₁ = parts hs₁)
: some (part' hp₀ hp₁) = parts (hs₀ ++ hs₁) :=
sorry

lemma part_eq_parts_app_of_parts_parts {hp₀ hp₁ : heap} {hs₀ hs₁ : list heap}
  (H₁ : some hp₀ = parts hs₀)
  (H₂ : some hp₁ = parts hs₁)
: part hp₀ hp₁ = parts (hs₀ ++ hs₁) :=
sorry

lemma parts_singleton (hp : heap)
: some hp = parts [hp] :=
sorry

def heap.insert (hp : heap) (p : pointer) (v : word) : heap
 | q := if p = q then some v else hp q

lemma part'_insert (hp hp' : heap) (p : pointer) (v : word)
  (h₀ : hp.insert p v ## hp')
  (h₁ : hp ## hp')
: part' (hp.insert p v) hp' = (part' hp hp').insert p v :=
sorry

lemma maplet_insert_disjoint_iff (p : pointer) (v v' : word) (hp : heap)
: (maplet p v).insert p v' ## hp ↔ maplet p v ## hp :=
sorry

namespace tactic.interactive

open tactic

/-- Given `h : heap`, find `hs : list heap` such that `some h = parts hs` -/
meta def flat_heap_expr : expr → tactic (dlist expr × expr)
 | `(part' %%h₀ %%h₁ %%Hd) :=
do (hs₀,p₀) ← flat_heap_expr h₀,
   (hs₁,p₁) ← flat_heap_expr h₁,
   p ← to_expr ``(part'_eq_parts_app_of_parts_parts %%Hd %%p₀ %%p₁),
   return (hs₀ ++ hs₁,p)
 | h :=
do p ← to_expr ``(parts_singleton %%h),
   return (dlist.singleton h, p )

/-- Given `h : option heap`, find `hs : list heap` such that `h = parts hs` -/
meta def flat_opt_heap_expr : expr → tactic (dlist expr × expr)
 | `(part %%h₀ %%h₁) :=
do (hs₀,p₀) ← flat_heap_expr h₀,
   (hs₁,p₁) ← flat_heap_expr h₁,
   p ← to_expr ``(part_eq_parts_app_of_parts_parts %%p₀ %%p₁),
   return (hs₀ ++ hs₁,p)
 | e := fail "expecting expression of the form `part ?m ?m`"

meta def flatten_heap : tactic unit :=
do t ← target,
   (e₀,e₁) ← expr.is_eq t,
   (ls,p) ← flat_heap_expr e₁,
   h ← note `h none p,
   `[simp at h],
   asrt ← to_expr ``(some %%e₀ = some %%e₁),
   h' ← assert `h asrt,
   tactic.swap,
   tactic.injection h' >> assumption,
   h ← get_local `h,
   rewrite_target h,
   tactic.clear h,
   return ()

meta def eq_heap : tactic unit := do
do t ← target,
   (e₀, e₁) ← expr.is_eq t,
   (_,p₀) ← flat_opt_heap_expr e₀,
   (_,p₁) ← flat_opt_heap_expr e₁,
   rewrite_target p₀,
   rewrite_target p₁,
   `[apply parts_congr, simp],
   prove_perm

section

variables {hp hp₀ hp₁ hp₂ hp₃ : heap}
variables (d₀₁ : hp₀ ## hp₁)
variables (d₁₀ : hp₁ ## hp₀)
variables (d₂₃ : hp₂ ## hp₃)
variables (d₀₁₂₃ : disjoint (part' hp₀ hp₁ d₀₁) (part' hp₂ hp₃ d₂₃))
variables (h : some hp = parts [hp₀,hp₁,hp₂,hp₃])
include d₀₁ d₁₀ d₂₃ d₀₁₂₃ h
example : hp = part' (part' hp₀ hp₁) (part' hp₂ hp₃) d₀₁₂₃ :=
begin
  flatten_heap,
  apply h,
end

example : part  (part' hp₁ hp₀) (part' hp₂ hp₃) = part (part' hp₂ hp₃) (part' hp₀ hp₁)  :=
begin
  eq_heap
end
end

end tactic.interactive
