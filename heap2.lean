import separation.heap

universes u

noncomputable def part_  (h₀ h₁ : option heap) : option heap :=
h₀ >>= λ h, h₁ >>= part h

@[simp]
lemma some_part'
  (hp₀ hp₁ : heap)
  (h : hp₀ ## hp₁)
: some (part' hp₀ hp₁) = part_ (some hp₀) (some hp₁) :=
by { simp [part_,part,bind,option.bind,dif_pos, h], }

@[simp]
lemma heap_emp_part_
  (hp : heap)
: part_ (some heap.emp) (some hp) = some hp :=
sorry

@[simp]
lemma part__heap_emp
  (hp : heap)
: part_ (some hp) (some heap.emp) = some hp :=
sorry

lemma part__assoc
  (a b c : option heap)
: part_ (part_ a b) c = part_ a (part_ b c) :=
sorry

lemma part__comm
  (a b : option heap)
: part_ a b = part_ b a :=
sorry

instance : is_associative (option heap) part_ :=
⟨ part__assoc ⟩
instance : is_commutative (option heap) part_ :=
⟨ part__comm ⟩

lemma disjoint_of_is_some_part_
  {hp₀ hp₁ : heap}
  (h : (part_ (some hp₀) (some hp₁)).is_some)
: hp₀ ## hp₁ :=
sorry

lemma disjoint_of_part__eq_some
  {hp₀ hp₁ hp₂ : heap}
  (h : some hp₂ = (part_ (some hp₀) (some hp₁)))
: hp₀ ## hp₁ :=
sorry

lemma eq_part'_of_some_eq_part_
  (hp₀ hp₁ hp : heap)
  (h : some hp = part_ (some hp₀) (some hp₁))
: hp = part' hp₀ hp₁ (disjoint_of_part__eq_some h) :=
by { apply @option.no_confusion _ _ (some hp) (some _) _ id,
     simp [h], }

lemma is_some_of_is_some_part__right
  (hp₀ : option heap) {hp₁ : option heap}
  (h : (part_ hp₀ hp₁).is_some)
: hp₁.is_some :=
sorry

lemma is_some_of_is_some_part__left
  {hp₀ : option heap} (hp₁ : option heap)
  (h : (part_ hp₀ hp₁).is_some)
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

lemma opt_apl_part__maplet (hp : heap) (p : pointer) (v : word)
  (h : maplet p v ## hp)
: (opt_apl (part_ (some (maplet p v)) (some hp)) p) = some v :=
begin
  simp [part_,has_bind.bind,option.bind],
  rw [part,dif_pos,opt_apl,part',maplet,if_pos rfl],
  refl,
  assumption
end
