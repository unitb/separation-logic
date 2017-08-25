
import data.bitvec
import data.dlist
import util.logic
import util.control.applicative
import util.control.monad.non_termination
import ..separation.heap

universes u v w w'

open nat list function

namespace separation

structure hstate :=
  (heap : heap)
  (next : ℕ)
  (free : ∀ p, p ≥ next → heap p = none)

@[reducible]
def program := state_t hstate nonterm

export nonterm (run_to)

namespace program

variables {α : Type u} {β : Type}

section mfix

protected def le (x y : program β) : Prop :=
∀ i, x i ≤ y i

instance : has_le (program β) :=
 { le := program.le }

protected def le_refl (x : program β)
: x ≤ x :=
by { introv i, refl }

protected def le_antisymm (x y : program β)
  (h₀ : x ≤ y)
  (h₁ : y ≤ x)
: x = y :=
by { apply funext, intro i, apply le_antisymm (h₀ i) (h₁ i) }

protected def le_trans (x y z : program β)
  (h₀ : x ≤ y)
  (h₁ : y ≤ z)
: x ≤ z :=
by { intro i, apply le_trans (h₀ i) (h₁ i) }

instance : weak_order (program β) :=
 { le := program.le
 , le_refl := @program.le_refl β
 , le_antisymm := program.le_antisymm
 , le_trans := program.le_trans }

instance has_mono_program : has_mono program :=
 { to_monad := by apply_instance
 , le := by apply_instance
 , input_t  := hstate
 , result_t := λ α, α × hstate
 , run_to := λ α m i s s', nonterm.run_to (m s) i s'
 , run_to_imp_run_to_of_le := by { introv h, apply h } }

@[reducible]
protected def monotonic (f : (α → program β) → α → program β) :=
monotonic (λ rec, uncurry' $ f $ curry rec)

protected lemma lift_mono {α β} (f : (α → program β) → α → program β)
  (h : monotonic f)
: @monotonic nonterm _ (α × hstate) (β × hstate) $ λ rec, uncurry' (f $ curry rec) :=
begin
  unfold monotonic,
  intros v₀ i v' v1 v2 h' x,
  apply h,
  { intros x y,
    apply h' }
end

protected def mfix {α : Type} {β : Type}
  (f : (α → program β) → α → program β)
  (Hf : monotonic f)
: α → program β :=
curry (@nonterm.fix (α × hstate) (β × hstate) (λ g, uncurry' (f $ curry g))
(program.lift_mono _ Hf))

-- @[reducible]
-- def monotonic2 {α : Type} {γ : Type} {β : Type}
--   (f : (α → γ → program β) → α → γ → program β) :=
-- monotonic (λ rec, uncurry' (f $ curry rec))

protected def program.mfix2 {α : Type} {α' : Type} {β : Type}
  (f : (α → α' → program β) → α → α' → program β)
  (Hf : monotonic2 f)
: α → α' → program β :=
curry $ program.mfix (λ g, uncurry' (f $ curry g)) Hf

def program.fix_unroll {α : Type} {β : Type}
  (f : (α → program β) → α → program β)
  (Hf : monotonic f)
: program.mfix f Hf = f (program.mfix f Hf) :=
begin
  admit
end

def program.fix2_unroll {α : Type} {α' : Type} {β : Type}
  (f : (α → α' → program β) → α → α' → program β)
  (Hf : monotonic2 f)
: program.mfix2 f Hf = f (program.mfix2 f Hf) :=
begin
  admit
end

end mfix

end program

namespace program

section

variables {α β γ : Type}
variable f  : α → program γ
variable g  : (α → program β) → α → γ → program β
variable Hg  : ∀ y, monotonic (λ rec x, g rec x y)

include Hg

protected lemma bind_monotonic'
: monotonic (λ rec x, f x >>= g rec x) :=
sorry

end

section

variables {α : Type}
variables {β : Type}
variable f : (α → program β) → α → program β
variable g : (α → program β) → α → β → program β
variable Hf : monotonic (λ rec x, f rec x)
variable Hg : ∀ y, monotonic (λ rec x, g rec x y)
include Hf

protected lemma pre_fixpoint (x : α)
: program.mfix f Hf x ≤ f (program.mfix f Hf) x :=
sorry

include Hg

protected lemma bind_monotonic
: monotonic (λ rec x, f rec x >>= g rec x) :=
sorry

end

end program

instance has_fix_program : has_fix program :=
 { to_has_mono := by apply_instance
 , mfix := λ α β f h, @program.mfix α β _ h
 , bind_monotonic := by { introv h₀ h₁, apply program.bind_monotonic _ _ h₀ h₁, }
 , bind_monotonic' := @program.bind_monotonic'
 , pre_fixpoint := by { introv, apply program.pre_fixpoint } }

def read (p : pointer) : program word := do
h ← state_t.read,
state_t.lift $ option.rec_on (h.heap p) nonterm.diverge return

meta def decide : tactic unit :=
`[apply of_as_true, exact trivial]

def read_nth (p : pointer) (i j : ℕ) (h : i < j . decide) : program word :=
read $ p+i

example : ∀ x : read_nth 100 1 2 = return 3, true :=
by { intro, trivial }

def write (p : pointer) (v : word) : program unit := do
s ← state_t.read,
if h : (s.heap p).is_some then
  state_t.write
    { s with
      heap := (λ q : pointer, if p = q then some v else s.heap q)
    , free :=
      begin
        intros q h',
        by_cases p = q with h'',
        { rw if_pos h'',
          exfalso, subst q,
          have h₃ := s.free p h',
          admit },
        { rw if_neg h'', apply s.free _ h' }
      end }
else state_t.lift nonterm.diverge

def write_nth (p : pointer) (i j : ℕ) (v : word) (h : i < j . decide) : program unit :=
write (p+i) v

def modify (p : pointer) (f : word → word) : program unit :=
read p >>= write p ∘ f

def modify_nth (p : pointer) (i j : ℕ) (f : word → word) (h : i < j . decide) : program unit :=
modify (p+i) f

def alloc (vs : list word) : program pointer := do
s ← state_t.read,
let r := s.next,
state_t.write
  { s with next := s.next + vs.length,
           heap := heap.mk r vs <+ s.heap,
           free := sorry },
return r

def alloc1 (v : word) : program pointer := do
alloc [v]

def free (p : pointer) (ln : ℕ) : program unit := do
s ← state_t.read,
state_t.write
  { s with heap := heap.delete p ln s.heap,
           free := sorry }

def free1 (p : pointer) : program unit := do
free p 1

def copy (p q : pointer) : program unit := do
v ← read q,
write p v

end separation
