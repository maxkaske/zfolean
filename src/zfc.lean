
import fol
import data.set

/-!
# ZFC set theory

In this file we define the signature and axioms of Zermelo–Fraenkel with axiom of choice.
and give a natural deduction proof of the induction principle in its set theoretical form.

We also briefly discuss how statements about named variables like 
  "φ is a formula with B not free"
in the formulation of the axiom schemes of separation and replacement
can be translated to De Bruijn variables using lifts.

## Main results

- `omega_smallest_inductive_provable_within_zfc`: 
    we show that ZFC proves that ω is the smallest inductive set. a direct consequence of
- `omega_smallest_inductive`: 
    a natural deduction proof that ω is the smallest inductive set

## References

* [H.D. Ebbinghaus, *Einführung in die Mengenlehre*] [EBB03] 
  -- for its classical development of ZFC
-/

namespace zfc
open fol

universe variable u

-- for inserting elements into a data.set
local infix ` >> ` := insert

section zfc_language

/- We will use single predicate for membership and nothing else -/
inductive pred_symb : ℕ → Type u
| elem : pred_symb 2
inductive func_symb : ℕ → Type u

def 𝒮 : signature := { func_symb:= zfc.func_symb , pred_symb:= zfc.pred_symb }

-- Definition and notation for our predicate
@[simp] def memb (t₁ t₂: term 𝒮): formula 𝒮 := papp (papp (pred pred_symb.elem) t₁) t₂
infix ` ∈' `:100 := memb

-- Predicates in our meta signature
def subset (X Y : term 𝒮) : (formula 𝒮) := ∀' ((#0 ∈' (X ↑ 1 ＠  0)) →' (#0 ∈' (Y ↑ 1 ＠  0)))
infix ` '⊆ `:100 := subset

def is_successor_of( X Y: term 𝒮 ) : formula 𝒮 
  := ∀'( (#0 ∈' (X ↑ 1 ＠ 0 )) ↔' ((#0 ∈' (Y ↑ 1 ＠  0)  ∨' (#0 =' (Y ↑ 1 ＠  0) ))))
infix ` is_successor_of' `:100 := is_successor_of

def is_empty (x : term 𝒮) : formula 𝒮 := ∀' ( (#0 ∈' (x ↑ 1 ＠ 0) ) ↔' ¬'(#0 =' #0) )
postfix ` is_empty'`:100 := is_empty 

def is_inductive (x : term 𝒮) : formula 𝒮 := (∀' (#0 is_empty' →' (#0 ∈' (x ↑ 1 ＠ 0))))      
  ∧' ( ∀'(#0 ∈' (x ↑ 1 ＠  0) →' (∀' (( #0 is_successor_of' #1) →' (#0 ∈' (x ↑ 2 ＠ 0))))))
postfix ` is_inductive'`:100 := is_inductive 

@[simp] def unique_in_var0 (φ: formula 𝒮) : formula 𝒮 
  :=  ∀' ∀' (  (φ  ↑ 1 ＠ 1 ) ∧' ( φ ↑ 1 ＠ 0 ) →' (#0 =' #1) )

@[simp] def unique_ex (φ : formula 𝒮) : formula 𝒮 
  := (∃'φ) ∧' (unique_in_var0 φ)
prefix `∃!`:110 := unique_ex 

end zfc_language


/-
-- some notation for the pretty printer to make debugging easier
-- before
#check  #1 ∈' #2                        -- #1 ∈' #2 : formula 𝒮
#reduce #1 ∈' #2                        -- ((pred pred_symb.elem).papp #1).papp #2
#reduce (#0 ∈' #2 ∧' #1 ∈' #2) ↑ 1 ＠ 1 -- ((pred pred_symb.elem).papp #0).papp #3 ∧' ((pred pred_symb.elem).papp #2).papp #3
notation s ` '∈ `:100 t := papp (papp (pred pred_symb.elem) s) t
-- after
#check  #1 ∈' #2                        -- #1 ∈' #2 : formula 𝒮
#reduce #1 ∈' #2                        -- #1 ∈ #2
#reduce (#0 ∈' #2 ∧' #1 ∈' #2) ↑ 1 ＠ 1 -- (#0 ∈ #3) ∧' #2 ∈ #3
-- much better
-/


section zfc_axioms
namespace separation
/-
  The separation axiom scheme is defined as the closure* of
    `∀A ∃B ∀x ( x ∈ B ↔ x ∈ A ∧ φ)` (1)
  for all formulas `φ` such that `B` is not free in `φ`.
  Ignoring variable names we see that the existential quantifier 
  binds variables of `φ` pointing to `1`.
  We can avoid such bindings by simply requiring that 
    `φ = ψ ↑ 1 ＠ 1` 
  for a formula `ψ`.
  On the other hand, if no index points to `1`, then one can check that
    `φ = φ[#0/1] ↑ 1 ＠ 1`**,
  reducing the side condition to a question about lifts.
  As an added bonus this allows us to state the axiom of separation 
  without any side condition as the closure of the formula below.

  (*) See further below.
  (**) Exercise 1: Generalize this and proof it in lean.
-/
@[simp] def formula (φ : formula 𝒮): formula 𝒮 
  := ∀' ∃' ∀' ((#0 ∈' #1)  ↔' (#0 ∈' #2 ∧' (φ  ↑ 1 ＠  1)))

/-
  To define the closure of (1) we usually state separation in terms of formulas φ(x, A, x₁, ... , xₙ)
  with free variables among (but not necessarily exactly) x, A, x₁, ... , xₙ.
  The closure is then given by
    `∀xₙ ... ∀x₁ ∀A ∃B ∀x ( x ∈ B ↔ x ∈ A ∧ φ)`. (1')
  For our De Bruijn representation of variables this translates to `φ_h: closed (n+2) φ`,
  so `formula φ` has no n-free variables (see lemma below) and its closure (as defined in fol)
  gives us an De Bruijn version of (1') and invariance under lifts.
-/

lemma closed{k} {φ} (H: closed (k+2) φ) : closed k (formula φ)  :=
begin
  have h₁: ¬ k + 3 ≤ 2, by linarith,
  have h₂: 1 ≤ k+2, by linarith,
  have h₃:  φ ↑  1 ＠  1 ↑ 1  ＠ (k + 3) = φ ↑ 1 ＠ 1,
    begin  rw ←(lift_lift φ 1 1 h₂), congr, exact H, end,
  simp[h₁, h₃],
end

def sentence  (φ : fol.formula 𝒮) {n : ℕ} (φ_h: formula.closed (n+2) φ) : fol.formula 𝒮 
  := formula.closure (formula φ) (closed φ_h)

lemma is_sentence {k : ℕ} (φ  : fol.formula 𝒮) (H: fol.formula.closed (k+2) φ) :
  (sentence φ H) is_sentence' := begin exact closure_is_sentence (closed H) end

lemma lift_sentence (φ) (n) (φ_h: fol.formula.closed (n+2) φ) (m i) 
  : (sentence φ φ_h) ↑ m ＠  i = sentence φ φ_h := lift_sentence_id (is_sentence _ _)


/- To following definition and lemmas are used to make future proofs more explicit and readable. -/
lemma mem {Γ:set $ fol.formula 𝒮} (φ) (k) (φ_h: formula.closed (k+2) φ) 
  {ψ} (h : ψ = sentence φ φ_h) (H: (sentence φ φ_h) ∈ Γ) : ψ ∈ Γ :=
begin subst h, exact H, end 

def scheme : set $ fol.formula 𝒮 := 
  { (sentence φ φ_h) |  (φ : fol.formula 𝒮) (k: ℕ) (φ_h : formula.closed (k+2) φ) } 

lemma mem_scheme (φ : fol.formula 𝒮) {k : ℕ} (φ_h: fol.formula.closed (k+2) φ)
  : sentence φ φ_h ∈ scheme := begin existsi [φ, k, φ_h], refl end
 
end separation


namespace replacement
/-
  The replacement axiom scheme is defined as the closure of
    `∀A ( ∀x(x ∈ A → ∃!y φ) → ∃B ∀x (x ∈ A →  ∃y (y ∈ B ∧ φ)` (1)
  for all formulas φ such that B is not free in φ.
  Observe that in this case the the quantifier before B binds variables pointing to 2.
  Thus the side condition can be stated as
    `φ = ψ ↑ 1 ＠ 2` 
  for a formula `ψ` and we obtain our axiom scheme as the closure of the formula below.
-/
@[simp] def formula (φ: formula 𝒮) := 
  (∀'( ∀'(#0 ∈' #1 →' ∃!φ) →' ( ∃' ∀' ( #0 ∈' #2 →' (∃' (#0 ∈' #2 ∧' (φ ↑ 1 ＠ 2))))))) 

/-
  To define the closure of (1) we usually state replacement in terms of formulas φ(x, y, A, x₁, ... , xₙ)
  with free variables among (but not necessarily exactly) x, y, A, x₁, ... , xₙ.

  This then translates to `φ_h: closed (n+3) φ` and we can proceed as in the case of separation.
-/
lemma closed {k} {φ} (H: closed (k+3) φ) : closed k (formula φ) :=
begin
  have : ¬ k+4 ≤ 3, by linarith,
  have : ¬ k+4 ≤ 2, by linarith,
  have : ¬ k+3 ≤ 2, by linarith,
  have h₁ : 0 ≤ k+3, from (k+3).zero_le,
  have h₂ : 1 ≤ k+3, by linarith,
  have h₃ : 2 ≤ k+3, by linarith,
  have H₁ : (φ ↑ 1 ＠ 0) ↑ 1 ＠  (k + 4) = φ  ↑  1 ＠ 0, from
    begin rw ←(lift_lift φ 1 1 h₁), congr, exact H, end,
  have H₂: (φ ↑ 1 ＠ 1) ↑ 1 ＠ (k + 4) = φ ↑ 1 ＠ 1, from
    begin rw ←(lift_lift φ 1 1 h₂), congr, exact H, end,
  have H₃: (φ ↑ 1 ＠ 2) ↑ 1 ＠ (k + 4) = φ ↑ 1 ＠ 2, from
    begin rw ←(lift_lift φ 1 1 h₃), congr, exact H, end,
  rw closed at H, clear h₂,
  simp[*, closed],
end 

def sentence  (φ : fol.formula 𝒮) {n : ℕ} (φ_h: formula.closed (n+3) φ) : fol.formula 𝒮 
  := formula.closure (formula φ) (closed φ_h)

lemma is_sentence  (φ : fol.formula 𝒮) {k : ℕ} (H: fol.formula.closed (k+3) φ) :
  (sentence φ H) is_sentence' := begin exact closure_is_sentence (closed H) end

lemma lift_sentence (φ) (n) (φ_h: fol.formula.closed (n+3) φ) (m i) 
  : (sentence φ φ_h) ↑ m ＠  i = sentence φ φ_h := lift_sentence_id (is_sentence _ _)

/- To following definition and lemmas are used to make future proofs more explicit and readable. -/
lemma mem {Γ:set $ fol.formula 𝒮} {ψ} (φ) {k} (φ_h: formula.closed (k+3) φ) 
  (h : ψ = sentence φ φ_h) (H: (sentence φ φ_h) ∈ Γ) : ψ ∈ Γ :=
begin subst h, exact H end 

def scheme : set $ fol.formula 𝒮 := 
  { (sentence φ φ_h) |  (φ : fol.formula 𝒮) (k: ℕ) (φ_h : fol.formula.closed (k+3) φ) }

lemma mem_scheme (φ : fol.formula 𝒮) {k : ℕ} (φ_h: fol.formula.closed (k+3) φ)
  : sentence φ φ_h ∈ scheme := begin existsi [φ, k, φ_h], refl, end

end replacement


/- ∀b ∀a (∀x (x ∈ a ↔ x ∈ b) → a = b) -/
@[simp] def extensionality  : formula 𝒮 := ∀' ∀' ( (∀' (#0 ∈' #1 ↔' #0 ∈' #2)) →' (#0 =' #1) )
/- ∀b ∀a ∃A ∀x (x = a ∨ x = b → x ∈ A) -/
@[simp] def pair_ax         : formula 𝒮 := ∀' ∀' ∃' ∀' ( (#0 =' #2) ∨' (#0 =' #3) →' (#0 ∈' #1))
/- ∀F ∃A ∀x (∃y (x ∈ y ∧ y ∈ x) → x ∈ A)  -/
@[simp] def union_ax        : formula 𝒮 := ∀' ∃' ∀' ((∃'( #1 ∈' #0 ∧' #0 ∈' #3)) →' (#0 ∈' #1) )
/- ∀y ∃A ∀x (x ⊆ y → x ∈ A) -/
@[simp] def power_ax        : formula 𝒮 := ∀' ∃' ∀' ((#0 '⊆ #2) →' (#0 ∈' #1))
/-- ∃w ( w is inductive) -/
@[simp] def infinity_ax     : formula 𝒮 := ∃' (#0 is_inductive')
/- x ( ¬(x is empty) → ∃y(y ∈ x ∧ ¬(∃z (z ∈ y ∧ z ∈ x))) -/
@[simp] def regularity      : formula 𝒮 := 
  ∀' (¬'(#0 is_empty') →' (∃' ( (#0 ∈' #1) ∧' ¬' ∃'(#0 ∈' #1 ∧' #0 ∈' #2))))
/- For every set `X` of nonempty, pairwise disjoint sets, 
  there exists a set `Y` containg exactly one element of each element of `X`.

  ∀X (∀x ∀y ( x ∈ X ∧ y ∈ X → (¬(x is empty) ∧ (x=y ∨ ∀z ¬ (z ∈ x ∧ z ∈ y)))     
        → ∃Y ∀x (x ∈ X → ∃!z (z ∈ x ∧ z ∈ Y))    
-/
@[simp] def axiom_of_choice : formula 𝒮 :=
  ∀' ( ∀' ∀' ( #0 ∈' #2 ∧' #1 ∈' #2 →' ∃' (#0 ∈' #1) ∧' ( #0 =' #1 ∨'  ∀' ( ¬'( (#0 ∈' #1 ∧' #0 ∈' #2 )))))
      →' ∃' ∀' ( #0 ∈' #2 →' ∃! (#0 ∈' #1 ∧' #0 ∈' #2)))

/-- ∀A ∃B ∀x ( x ∈ B ↔ x ∈ A ∧ φ ↑ 1 ＠ 1) -/
@[simp] def separation_ax  (φ : formula 𝒮) {n} (φ_h: closed (n+2) φ) : formula 𝒮            
  := separation.sentence φ φ_h
/-- ∀A ( ∀x(x ∈ A → ∃!y φ) → ∃B ∀x (x ∈ A →  ∃y (y ∈ B ∧ φ) -/
@[simp] def replacement_ax (φ : formula 𝒮) {n} (φ_h: closed (n+3) φ) : formula 𝒮            
  :=replacement.sentence φ φ_h


/-- The axioms of ZFC set theory as set. -/
def zfc_ax : set $ formula 𝒮 := { extensionality, pair_ax, union_ax, power_ax, infinity_ax, 
                                  regularity, axiom_of_choice} 
                                    ∪ separation.scheme
                                    ∪ replacement.scheme

lemma zfc_ax_set_of_sentences: ∀ x ∈ zfc_ax, (x is_sentence') :=
begin
  intros φ  h,
  repeat{cases h,};
  try {unfold sentence closed, refl, },
  { cases h_h with n hn,
    cases hn with h hh,
    subst hh, apply separation.is_sentence, },
  { cases h_h with n hn,
    cases hn with h hh,
    subst hh, apply replacement.is_sentence, },
end

lemma lift_zfc_ax {m i} : (λ ϕ: formula 𝒮, ϕ ↑ m ＠ i) '' zfc_ax = zfc_ax 
  := lift_set_of_sentences_id zfc_ax_set_of_sentences

/- We mainly use the following lemmas to make usage of axioms more explicit in the text. -/
-- for arbitrary sets
lemma extensionality_mem {Γ: set $ formula 𝒮}{φ}(h: φ = extensionality)(H: extensionality ∈ Γ) : φ ∈ Γ :=
begin subst h, exact H end
lemma pair_ax_mem {Γ: set $ formula 𝒮} {φ} (h: φ = pair_ax) (H: pair_ax ∈ Γ)    : φ ∈ Γ :=
begin subst h, exact H end
lemma union_ax_mem {Γ: set $ formula 𝒮} {φ} (h: φ = union_ax) (H: union_ax ∈ Γ) : φ ∈ Γ :=
begin subst h, exact H end
lemma power_ax_mem {Γ: set $ formula 𝒮} {φ} (H: power_ax ∈ Γ) (h: φ = power_ax) : φ ∈ Γ :=
begin subst h, exact H end
lemma infinity_ax_mem {Γ: set $ formula 𝒮} {φ} (h: φ = infinity_ax) (H: infinity_ax ∈ Γ)  : φ ∈ Γ :=
begin subst h, exact H end
lemma regularity_mem {Γ: set $ formula 𝒮}{φ}(h: φ = regularity)(H: regularity ∈ Γ) : φ ∈ Γ :=
begin subst h, exact H end
lemma aoc_mem {Γ: set $ formula 𝒮}{φ}(h: φ = axiom_of_choice)(H: axiom_of_choice ∈ Γ) : φ ∈ Γ :=
begin subst h, exact H end

-- for zfc_ax
lemma extensionality_mem_zfc_ax : extensionality ∈ zfc_ax := by simp[-extensionality, zfc_ax]
lemma pair_ax_mem_zfc_ax : pair_ax ∈ zfc_ax := by simp[-pair_ax, zfc_ax]
lemma union_ax_mem_zfc_ax : union_ax ∈ zfc_ax := by simp[-union_ax, zfc_ax]
lemma power_ax_mem_zfc_ax : power_ax ∈ zfc_ax := by simp[-power_ax, zfc_ax]
lemma infinity_ax_mem_zfc_ax : infinity_ax ∈ zfc_ax := by simp[-infinity_ax, zfc_ax]
lemma regularity_mem_zfc_ax : regularity ∈ zfc_ax := by simp[zfc_ax]
lemma aoc_mem_zfc_ax : axiom_of_choice ∈ zfc_ax := by simp[zfc_ax]

namespace separation
lemma mem_zfc_ax (φ k) (φ_h: formula.closed (k+2) φ) : sentence φ φ_h ∈ zfc_ax :=
begin simp[-sentence, zfc_ax, mem_scheme], end
end separation

namespace replacement
lemma mem_zfc_ax (φ k) (φ_h: formula.closed (k+3) φ) : sentence φ φ_h ∈ zfc_ax :=
begin simp[-sentence, zfc_ax, mem_scheme], end
end replacement

end zfc_axioms

section zfc_proofs
/- 
  ### On comments inside the proofs
  The first proof is the only one with excessive use of comments/
  In the following proofs we will give readable goals 
  and the current variable environment, hoping that the context should be clear.

  for example the current goal might look like
    (λ (ϕ : formula 𝒮), ϕ ↑ 1 ＠ 0) ''
        (∀'(#0 ∈' #1 ↔' #0 =' #3 ∨' #0 =' #3) >>
          (λ (ϕ : formula 𝒮), ϕ ↑ 1 ＠ 0) '' ((λ (ϕ : formula 𝒮), ϕ ↑ 1 ＠ 0) '' zfc_ax)) ⊢
      ((#0 ∈' #1 →' #0 =' #3) ↑ 1 ＠ (0 + 1 + 1))[#0 ⁄ 0 + 1]
  while the comment reads
  `a {a,a} x ⊢ x ∈ {a,a} → x = a` 
  * a {a,a} x are sets (usually with associated properties hidden in the context, or obvious from the name)
  * indices pointing to 0 talk about x
  * indices pointing to 1 talk about {a,a}
  * indices pointing to 2 talk about a
  * the goal should be read as `x ∈ {a,a} → x = a` 
  -//- 
  Lastly we use "-- meta" to denote parts of a proof not directly involving terms of type `fol.proof`.
  This is usually the case at the leaves of of a natural deduction proof tree
  where we have to reason about formulas being equal or element of the context.
-/

/--
  A formal proof that for all sets `b,a` there exists a set containing exactly `a` and `b`.

  Informally: `zfc_ax ⊢ ∀b ∀a ∃A ∀x (x ∈ A ↔ x=a ∨ x=b)`
-/
def pairset_ex: zfc_ax ⊢ ∀' ∀' ∃' ∀' ( (#0 ∈' #1) ↔' (#0 =' #2) ∨' (#0 =' #3)) :=
begin
  apply allI, -- given a
  apply allI, -- given b
  apply exE ∀'( (#0 =' #2) ∨' (#0 =' #3) →' (#0 ∈' #1)), -- let A be a set containing b and a,
  { -- such a set exists pair pairing: 
    apply allE' _ #0,         -- bind b   --(∃' ∀'( (#0 =' #2) ∧' (#0 =' #4) →' (#0 ∈' #1))) #0,
    apply allE' _ #1,         -- bind a  --( ∀' ∃' ∀'( (#0 =' #2) ∧' (#0 =' #3) →' (#0 ∈' #1))) #1,
    apply hypI,               -- this is a hypothesis
    -- meta
    simp only [lift_zfc_ax],
    apply pair_ax_mem_zfc_ax,
    simp[zfc_ax],
    all_goals { simp } },
  { -- now we can use A and its defining property for further arguments
    -- reminder: sets (in order) a b A
    apply exE (∀'( #0 ∈' #1 ↔' (#0 ∈' #2) ∧' (#0 =' #3 ∨' #0 =' #4))), -- let {b,a} be the set {x | x ∈ A ∧ (x=b ∨ x=a)}
    { -- such a set exists by separation:
      apply allE' _ #0,                                           -- bind A
      apply allE' _ #1,                                           -- bind b
      apply allE' _ #2,                                           -- bind a
      apply hypI,                                                 -- this is a hypothesis
      -- meta
      apply separation.mem (#0 =' #2 ∨' #0 =' #3) 2 (rfl) (rfl),   -- an instance of separation
      simp only [lift_zfc_ax],
      right, apply separation.mem_zfc_ax,
      all_goals{ simp[alls] }, refl },
    { -- variables (in order) a b A { x | x ∈ A ∧ (x=b ∨ x=a)}
      apply exI #0, -- put X := {b,a}:= { x | x ∈ A ∧ (x=b ∨ x=a)} , we need to show that it satisfies the defining property
      apply allI,
      -- stack : a b A {b,a} x
      apply andI, 
      { -- ⊢ x ∈ {b,a} → x=b ∨ x=a
        apply impI, -- assume x ∈ {b,a} we want to show x=b ∨ x=a
        apply andE₂ (#0 ∈' #2), -- it suffices to show  x ∈ A ∧ (x=b ∨ x=a)
        apply impE_insert,  -- moreover it suffices to show x ∈ {b,a} →  x ∈ A ∧ (x=b ∨ x=a)
        apply iffE_r,      -- it suffices to show  x ∈ {b,a} ↔ x ∈ A ∧ (x=b ∨ x=a)
        apply allE_var0,   -- bind x
        apply hypI,         -- then this is a hypothesis, namely the defining property of  { x | x ∈ A ∧ (x=b ∨ x=a)
        -- meta
        simp only [set.image_insert_eq], 
        apply set.mem_insert, },
      { -- ⊢ x ∈ {b,a} ← x=b ∨ x=a
        apply impI,             -- assume x=b ∨ x=a, we need to show x ∈ {b,a}
        apply impE (#0 ∈' #2),  -- it suffices to show x ∈ A and x ∈ A → x ∈ {b,a}
        { -- first we show x ∈ A
          apply impE ((#0 =' #3) ∨' (#0 =' #4)), -- it suffices to show x = b ∨ x=a and x = b ∨ x=a → x ∈ A
          { -- we show x = b ∨ x = a
            apply hypI1 },  -- which is true by assumption
          { -- we show  x = b ∨ x = a → x ∈ A
            apply allE_var0, -- if we bind x
            apply hypI,       -- then this is how A was defined
            -- meta
            simp only [set.image_insert_eq],
            right, right, apply set.mem_insert } },
        { -- next we show x ∈ A → x ∈ {b,a}
          apply impI,   -- assume x ∈ A
          apply impE (#0 ∈' #2 ∧' ((#0 =' #3) ∨' (#0 =' #4))), -- then it suffices to show ...
          { -- x ∈ A ∧ x=0 ∨ x=b 
            apply andI, -- we need to show ...
            { -- ⊢ x ∈ A
              apply hypI1 }, -- by assumption
            { -- ⊢ x = 0 ∨ x=b
              apply hypI2 } },-- by assumption
          { -- ⊢ x ∈ A ∧ x=0 ∨ x=b → x ∈ {b,a}
            apply iffE_l, -- it suffices to show x ∈ {b,a} ↔ x ∈ A ∧ x=0 ∨ x=b 
            apply allE_var0,  -- binding x
            apply hypI,        -- this how we defined {b,a} in the first place
            -- meta
            simp only [set.image_insert_eq], 
            right, right, apply set.mem_insert } } } } },
end

/--
  Formal proof that an empty set exists.

  Informally: `zfc_ax ⊢ ∃A (∀x ( x ∈ A ↔ x≠x )) `
-/
def emptyset_ex : zfc_ax ⊢ ∃' (#0 is_empty'):=
begin
  -- consider the set { x | x ∈ A ∧ ¬'(#0 =' #0 ) }
  apply exE ∀'(#0 ∈' #1 ↔' #0 ∈' #2 ∧' ¬'(#0 =' #0 )),
  { -- such a set exists by separation
      apply allE_var0,           -- bind A
      apply hypI,                 -- then this is true by separation
      apply separation.mem (¬'(#0 =' #0 )) 0 (rfl) (rfl),
      apply separation.mem_zfc_ax, },
  { -- ⊢ ∃X ∀x ( x ∈ X ↔ ¬ (x = x) ) 
    apply exI #0, -- Put X:={ x | x ∈ A ∧ ¬'(#0 =' #0 ) }
    apply allI,   -- given x
    apply andI,
    { -- ⊢  x ∈ X → ¬ (x = x)
      apply impI,
      apply andE₂ _,
      apply impE_insert,
      apply iffE_r,
      apply allE_var0,
      apply hypI,
      -- meta
      simp only [set.image_insert_eq],
      left, refl },
    { -- ⊢ ¬ (x = x) →  x ∈ X 
      apply impI,
      apply botE,
      apply impE (#0 =' #0),
      apply eqI,
      apply hypI,
      -- meta
      left, refl } },
end

/--
  Formal proof that for all sets `a` there exists a set containing just `a`.

  Informally: `zfc_ax ⊢ ∀a ∃A (∀x ( x ∈ A ↔ x = a )) `
-/
def singleton_ex : zfc_ax ⊢ ∀' ∃' ∀' ( #0 ∈' #1 ↔' #0 =' #3) :=
begin
  apply allI, --given a
  apply exE ∀' ( #0 ∈' #1 ↔' #0 =' #3 ∨' #0 =' #3), -- have the set {a,a}
  { -- a ⊢ ∃A ( A = {a,a}) 
    apply allE' _ #1,
    apply allE' _ #1,
    rw [lift_zfc_ax],
    apply pairset_ex,
    -- meta
    dsimp, refl,
    dsimp, refl },
  { -- a ⊢ ∃ A ∀x (x ∈ A ↔ x = a)
    apply exI #0, -- put `A := {a,a}`
    apply allI,   -- given x
    apply andI,
    { -- a {a,a} x ⊢ x ∈ {a,a} → x = a
      apply impI, -- assume `x ∈ {a,a}`
      apply orE (#0 =' #3) (#0 =' #3), -- suffices to show (x = a) ∨ ( x = a)
      { -- a {a,a} x ⊢ x = a ∨ x = a
        apply impE_insert,
        apply iffE_r,
        apply allE_var0,
        apply hypI,
        -- meta
        simp only [set.image_insert_eq], 
        left, refl },
      { -- assume `x = a`
        -- a {a,a} x⊢ x = a
        apply hypI1 },
      { -- assume `x = a`
        -- a {a,a} x ⊢ x = a
        apply hypI1 } },
    { -- a {a,a} x ⊢ x = a → x ∈ {a,a}
      apply impI, -- assume `x = a`
      apply impE ((#0 =' #3) ∨' (#0 =' #3)),
      { -- a {a,a} ⊢ x=a ∨ x=a
        apply orI₁,
        apply hypI1 },
      { -- a {a,a} x ⊢ x=a ∨ x=a → x ∈ {a,a}
        apply iffE_l,
        apply allE_var0,
        apply hypI,
        -- meta
        simp only [set.image_insert_eq], 
        right, left, refl } } }
end

/--
  Proof scheme. 
  Provides a formal proof of uniqueness of y
  satisfying formulas of the form `∀x (x ∈ y ↔ φ )`,
  provided `y` is not free in `φ`.

  Informally : {extensionality} ⊢ ∀y₁ ∀y₀ ( y₀ = { x | φ } ∧ y₁ = { x | φ } → y₀ = y₁)
-/
def extensionality_implies_uniqueness (φ : formula 𝒮)
  : {extensionality} ⊢ unique_in_var0  ∀'(#0 ∈' #1 ↔' (φ ↑ 1 ＠ 1)) :=
begin
  apply allI, -- y₁
  apply allI, -- y₀
  apply impI, -- assume `∀ x ( x ∈ y₀ ↔ φ(x, y₀)) ∧ ∀ x (x ∈ y₁ ↔ φ(x,y₁))`
  apply impE (∀' (#0 ∈' #1 ↔' #0 ∈' #2)), 
  { -- y₁ y₀ ⊢ (∀' (#0 ∈' #1 ↔' #0 ∈' #2))
    apply allI, -- x
    apply iffI_trans (φ ↑ 2 ＠  1), 
    { -- y₁ y₀ x ⊢ x ∈ y₀ ↔ φ (x, y₀)
      apply allE_var0, 
      apply andE₁ _ , 
      apply hypI, 
      -- meta argument
      simp [set.image_insert_eq],
      simp [subst_var0_for_0_lift_by_1, lift_lift_merge φ 1] },
    { -- y₁ y₀ x ⊢ φ (x, y₁) ↔ x ∈ y₁
      apply iffI_symm, 
      apply allE_var0, 
      apply andE₂ _ , 
      apply hypI,
      -- meta argument
      simp [set.image_insert_eq] } },
  { -- y₁ y₀ ⊢ ∀ x (x ∈ y₀ ↔ x ∈ y₁) → y₀ = y₁
    apply allE_var0,
    apply allE' _ #1,
    apply weak1,
    apply hypI, 
    -- meta argument
    simp,
    simp, },
end

/--
  QoL version of `extensionality_implies_uniqueness`

  Informally : `Γ ⊢ ∀y₁ ∀y₀ (ψ(y₀) ∧ ψ(y₁) → y₀ = y₁`,
  provided  `ψ(y) = ∀x (x ∈ y ↔ φ )`, `y` not free in `φ` and `extensionality ∈ Γ`.
-/
def extensionality_implies_uniqueness' {Γ} (φ) {ψ} (h: ψ = ∀'(#0 ∈' #1 ↔' (φ ↑ 1 ＠ 1) ) ) (H: extensionality ∈ Γ)  
  : Γ ⊢ unique_in_var0 ψ :=
begin
  subst h,
  apply weak_singleton extensionality (extensionality_implies_uniqueness φ),
  exact H,
end

/--
  `n`-closure variant of `extensionality_implies_uniqueness` 

  Informally : `{extensionality} ⊢ ∀xₙ ... ∀x₁ ∀y₁ ∀y₀ ( y₀ = { x | φ } ∧ y₁ = { x | φ } → y₀ = y₁)`
-/
def extensionality_implies_uniqueness_alls  (n)  (φ : formula 𝒮)
  : {extensionality} ⊢ alls n (unique_in_var0 ∀'(#0 ∈' #1 ↔' (φ ↑ 1 ＠ 1))) :=
begin
  apply allsI,
  apply extensionality_implies_uniqueness' φ (rfl),
  rw set.mem_image,
  use extensionality,
  exact ⟨ set.mem_singleton _ , rfl ⟩,
end

/--
  Formal proof that for all sets `b,a` the pair set `{a,b}` exists and is unique.

  Informally: `zfc_ax ⊢ ∀b ∀a ∃!A (∀x (x ∈ A ↔ x = a ∨ x = b))`
-/
def pairset_unique_ex : zfc_ax ⊢ (∀' ∀' ∃! ∀' ((#0 ∈' #1) ↔' (#0 =' #2) ∨' (#0 =' #3))) := 
begin
  apply allI, -- b
  apply allI, -- a
  simp only [lift_zfc_ax],
  apply andI,
  { -- b a ⊢ ∃A (∀x (x ∈ A ↔ x = a ∨ x = b)) 
    apply allE' _ #0,
    apply allE' _ #1,
    exact pairset_ex,
    simp, simp },
  { apply extensionality_implies_uniqueness' (#0 =' #1 ∨' #0 =' #2) (rfl),
    simp[-extensionality, zfc_ax] },
end
/--
  Formal proof that there exists an unique empty set.

  Informally: `zfc_ax ⊢ ∃! A (∀x ( x ∈ A ↔ ¬(x=x))) `
-/
def emptyset_unique_ex : zfc_ax ⊢ ∃! (#0 is_empty') := 
begin
  apply andI,
  { exact emptyset_ex, },
  { apply extensionality_implies_uniqueness' (¬'(#0 =' #0)) (rfl),
    simp[-extensionality, zfc_ax] },
end

/--
  Formal proof that for all sets `a` the singleton `{a}` exists and is unique.

  Informally: `zfc_ax ⊢ ∀a ∃!A (A = {a}) `
-/
def singleton_unique_ex : zfc_ax ⊢ ∀' ∃! ∀' ( #0 ∈' #1 ↔' #0 =' #3) :=
begin
  apply allsI 1,
  apply andI,
  { apply allsE' 1,
    exact singleton_ex, },
  { apply extensionality_implies_uniqueness' (#0 =' #2) (rfl),
    simp only [lift_zfc_ax],
    simp[-extensionality, zfc_ax] },
end

/--
  Proof scheme. Provides a formal proof of `∃B ∀x(x ∈ B ↔ φ)`
  from `∃B ∀x ( φ → x ∈ B)` by using the axiom of separation for `φ`.
-/
def separation_proof_scheme 
  (φ k) (φ_h₁: closed (k+2) φ)              -- given a formula φ(x_1,...,x_{k+1})
  (φ_h₂ : ∃ ϕ : formula 𝒮 , φ = ϕ ↑ 1 ＠ 1) -- such that the x₂ is not among its free variables
  {Γ} (h : separation_ax φ φ_h₁ ∈ Γ)        -- ...
  (H : Γ ⊢ alls k ∃' ∀'(φ →' (#0 ∈' #1)))
  : Γ ⊢ alls k (∃' ∀'((#0 ∈' #1) ↔' φ)) :=
begin
  apply allsI,
  apply exE ∀'( φ →' (#0 ∈' #1)), -- A with ∀ x (φ → x ∈ A) 
  { -- xₖ ... x₁ ⊢ ∃ A ∀x (φ → x ∈ A)
    apply allsE',
    exact H },
  { -- xₖ ... x₁ A ⊢ ∃ B ∀ x (x ∈ B ↔ φ )
    apply exE (∀'( (#0 ∈' #1) ↔' ( (#0 ∈' #2) ∧' (φ ↑ 1 ＠ 1 ) ))), -- B with ∀ x (x ∈ B ↔ x ∈ A ∧ φ )
    { -- xₖ ... x₁ A ⊢ ∃ B ∀ x (x ∈ B ↔ x ∈ A ∧ φ )
      apply weak1, 
      apply allsE' 1,
      apply allsE' k,
      rw [alls,alls],
      apply hypI,
      -- meta
      apply separation.mem φ k φ_h₁ (rfl),
      assumption, },
    { -- A B ⊢ ∃ B ∀ x (x ∈ B ↔ φ ) 
      apply exI #0,
      apply allI, -- x
      apply andI,
      { -- A B x ⊢ x ∈ B → φ
        apply impI, -- assume `x ∈ B`
        apply andE₂ (#0 ∈' #2),
        apply impE_insert,
        apply iffE_r,
        apply allE_var0,
        apply hypI,
        -- meta
        rw[set.image_insert_eq],
        left,
        cases φ_h₂ with ψ ψ_h,
        subst ψ_h,
        rw [subst_var0_lift_by_1, subst_var0_lift_by_1],
        rw [←lift_lift ψ _ _ (le_refl 1)], 
        refl },
      { --  A B x ⊢ φ → x ∈ B
        apply impI, -- assume `φ`
        apply impE (#0 ∈' #2),
        { --  A B x ⊢ x ∈ A
          apply impE (φ ↑ 1 ＠ 1),
          { -- A B x ⊢ φ 
            apply hypI,
            left,
            cases φ_h₂ with ψ ψ_h,
            subst ψ_h,
            rw [subst_var0_lift_by_1, ←lift_lift ψ _ _ (le_rfl)] },
          { -- A B x ⊢ φ → x ∈ A
            apply allE_var0, 
            apply hypI,
            -- meta
            simp only [set.image_insert_eq],
            right, right, left, refl } },
        { --  A B x ⊢ x ∈ A → x ∈ B
          apply impI, -- assume `x ∈ A` 
          apply impE (#0 ∈' #2 ∧' (φ ↑ 1 ＠ 1)),
          { -- A B x ⊢ x ∈ A ∧ φ 
            apply andI, 
            { -- A B x ⊢ x ∈ A
              apply hypI1 },
            { -- A B x ⊢ φ 
              apply hypI,
              -- meta
              right, left,
              cases φ_h₂ with ψ ψ_h,
              subst ψ_h,
              rw [subst_var0_lift_by_1, lift_lift ψ _ _ (le_rfl)] } },
          { -- A B x ⊢  x ∈ A ∧ φ → x ∈ B
            apply iffE_l, 
            apply allE_var0, 
            apply hypI,
            --meta
            simp only [set.image_insert_eq], 
            right, right, left,
            simp } } } } }
end


/--
  QoL version of `separation_proof_scheme`.
  
  Proof scheme. Provides a formal proof `ψ`
  from `∃B ∀x ( φ → x ∈ B)` and `ψ = ∃B ∀x(x ∈ B ↔ φ)`.
-/
def separation_proof_scheme' (φ) (k) (φ_h: closed (k+2) (φ ↑ 1 ＠ 1))
  {ψ : formula 𝒮} (ψ_h : ψ = alls k ∃' ∀'((#0 ∈' #1) ↔' (φ  ↑ 1 ＠ 1)))
  {Γ} (h : separation.sentence (φ ↑ 1 ＠ 1) φ_h ∈ Γ)
  (H: Γ ⊢ alls k ∃' ∀'( φ  ↑ 1 ＠ 1  →' (#0 ∈' #1))) 
  : Γ ⊢ ψ  :=
begin
  subst ψ_h,
  apply separation_proof_scheme (φ ↑ 1 ＠ 1) k φ_h (by use φ) h H,
end

/--
  Formal proof that for all sets `F` there exists a set 
  containing exactly the elements of its elements.

  Informally : `zfc_ax ⊢ ∀F ∃A ∀x (x ∈ A ↔ ∃y (x ∈ y ∧ y ∈ F))`
-/
def union_ex : zfc_ax ⊢ ∀' ∃' ∀' ( (#0 ∈' #1) ↔' ∃'(#1 ∈' #0 ∧' #0 ∈' #3) ):=
begin
  apply separation_proof_scheme' (∃'(#1 ∈' #0 ∧' #0 ∈' #2)) 1, -- enough to show one direction,
  { refl, },                                                    
  { apply separation.mem_zfc_ax, },                             -- which is an axiom
  { apply hypI,
    apply union_ax_mem_zfc_ax },
  { dsimp, refl, },
end

/--
  Formal proof that for all sets `F` the union `⋃F` exists and is unique.

  Informally : `zfc_ax ⊢ ∀F ∃!A (A = ⋃F)`
-/
def union_unique_ex : zfc_ax ⊢ ∀' ∃! ∀' ( (#0 ∈' #1) ↔' ∃'(#1 ∈' #0 ∧' #0 ∈' #3) ) := 
begin
  apply allI,
  simp only [lift_zfc_ax],
  apply andI,
  { apply allE' _ #0,
    exact union_ex,
    simp, },
  { apply extensionality_implies_uniqueness' (∃'(#1 ∈' #0 ∧' #0 ∈' #2)) (rfl),
    simp[-extensionality, zfc_ax] },
end

/--
  Formal proof that for all sets `y`  there exists a set 
  containing exactly all its subsets exists.

  Informally : `zfc_ax ⊢ ∀y ∃!A ∀x (x ∈ A  ↔ x ⊆ y)`
-/
def powerset_ex: zfc_ax ⊢ ∀' ∃' ∀' ((#0 ∈' #1) ↔' ( #0 '⊆ #2)) :=
begin
  apply separation_proof_scheme' (#0 '⊆ #1) 1,      -- enough to show oen direction
  { refl },
  { apply separation.mem_zfc_ax, },                  -- which is an axiom
  { apply hypI,
    apply power_ax_mem_zfc_ax, },
  { dsimp, refl, },
end

/--
  Formal proof that for all sets `y` the powerset `𝒫y` exists and is unique.

  Informally : `zfc_ax ⊢ ∀y ∃!A (A = 𝒫y)`
-/
def powerset_unique_ex : zfc_ax ⊢ ∀' ∃! ∀' ((#0 ∈' #1) ↔' ( #0 '⊆ #2)) := 
begin
  apply allI,
  simp only [lift_zfc_ax],
  apply andI,
  { apply allE_var0,
    exact powerset_ex, },
  { apply extensionality_implies_uniqueness' (#0 '⊆ #1) (rfl),
    simp[-extensionality, zfc_ax] },
end

/--
  Formal proof that for all sets `b, a` there exists a set containing exactly 
  the elements of `a` and `b`.

  Informally: `zfc_ax ⊢ ∀b ∀a ∃A ∀ x (x ∈ A  ↔ x ∈ a ∨ x ∈ b)`
-/
def binary_union_ex : zfc_ax ⊢ ∀' ∀' ∃' ∀' (#0 ∈' #1 ↔' #0 ∈' #2 ∨' #0 ∈' #3) :=
begin
  apply separation_proof_scheme' (#0 ∈' #1 ∨' #0 ∈' #2) 2, -- only need to show one direction
  { refl, },
  { apply separation.mem_zfc_ax, },
  { apply allI, -- b
    apply allI, -- a
    apply exE ∀'((#0 ∈' #1) ↔' (#0 =' #2) ∨' (#0 =' #3)),
    { -- b a ⊢ ∃B (B = {a,b}) 
      apply allE' _ #0,
      apply allE' _ #1,
      simp only [lift_zfc_ax],
      exact pairset_ex,
      simp, simp },
    { -- b a {a,b} ⊢ ∃A ∀x ( x ∈ a  ∨ x ∈ b → x ∈ A) 
      apply exE  ∀'( (#0 ∈' #1) ↔' ∃'(#1 ∈' #0 ∧' #0 ∈' #3)),
      { -- b a {a,b} ⊢ ∃B (B = ⋃{a,b})
        apply allE' _ #0,
        simp only [lift_zfc_ax],
        apply weak1,
        exact union_ex,
        simp },
      { -- b a {a,b} ⋃{a,b} ⊢ ∃A ∀x ( x ∈ a  ∨ x ∈ b → x ∈ A) 
        apply exI #0, -- let `A := ⋃{a,b}`
        apply allI, -- x
        apply impI, -- assume `x ∈ a ∨ x ∈ b`
        apply orE (#0 ∈' #3)  (#0 ∈' #4),
        { apply hypI1 },
        { -- assume `x ∈ a`
          -- b a {a,b} ⋃{a,b} ⊢ x ∈ ⋃{a,b}
          apply impE (∃'(#1 ∈' #0 ∧' #0 ∈' #3)),
          { -- b a {a,b} ⋃{a,b} ⊢ ∃y (x ∈ y ∧  y ∈ {a,b})
            apply exI #3,  -- put `y:= a`
            apply andI,
            { apply hypI1, },
            { -- b a {a,b} ⋃{a,b} ⊢ a ∈ {a,b}
              apply impE (#3 =' #3 ∨' #3 =' #4),
              { -- b a {a,b} ⋃{a,b} y ⊢ a = a ∨ a = b
                apply orI₁, 
                apply eqI, },
              { -- b a {a,b} ⋃{a,b} ⊢ a = a ∨ a = b → a ∈ {a,b}
                apply iffE_l,
                apply allE' _ #3,
                apply hypI,
                -- meta
                simp only [set.image_insert_eq],
                right, right, right, left, refl,
                simp } } },
          { -- b a {a,b} ⋃{a,b} y ⊢ ∃(x ∈ y ∧  y ∈ {a,b}) → x ∈ ⋃{a,b}
            apply iffE_l,
            apply allE_var0,
            apply hypI,
            -- meta
            simp only [set.image_insert_eq],
            right, right, left, refl } },
        { -- assume `x ∈ b`
          -- b a {a,b} ⋃{a,b} ⊢ x ∈ ⋃{a,b}
          apply impE (∃'(#1 ∈' #0 ∧' #0 ∈' #3)),
          { -- -- b a {a,b} ⋃{a,b} ⊢ ∃y (x ∈ y ∧  y ∈ {a,b})
            apply exI #4, -- put `y:=b`
            apply andI,
            { apply hypI1, },
            { -- b a {a,b} ⋃{a,b} ⊢ b ∈ {a,b}
              apply impE (#4 =' #3 ∨' #4 =' #4),
              { -- b a {a,b} ⋃{a,b} y ⊢ b = a ∨ b = b
                apply orI₂, 
                apply eqI, },
              { -- b a {a,b} ⋃{a,b} ⊢ b = a ∨ b = b → b ∈ {a,b}
                apply iffE_l,
                apply allE' _ #4,
                apply hypI,
                -- meta
                simp only [set.image_insert_eq],
                right, right, right, left, refl,
                simp } } },
          { -- b a {a,b} ⋃{a,b} y ⊢ ∃(x ∈ y ∧  y ∈ {a,b}) → x ∈ ⋃{a,b}
            apply iffE_l,
            apply allE_var0,
            apply hypI,
            -- meta
            simp only [set.image_insert_eq],
            right, right, left, refl } } } } },
  { dsimp, refl, },
end


/--
  Formal proof that for all sets `b, a` the binary union `a ∪ b` exists and is unique.

  Informally: `zfc_ax ⊢ ∀b ∀a ∃!A (A = a ∪ b)`
-/
def binary_union_unique_ex : zfc_ax ⊢ ∀' ∀' ∃! ∀' (#0 ∈' #1 ↔' #0 ∈' #2 ∨' #0 ∈' #3) := 
begin
  apply allsI 2,
  apply andI,
  { apply allsE' 2,
    exact binary_union_ex,},
  { apply extensionality_implies_uniqueness' (#0 ∈' #1 ∨' #0 ∈' #2) (rfl),
    simp only [lift_zfc_ax],
    simp[-extensionality, zfc_ax] }
end

/--
  Formal proof that for all sets `a` there exists a successor set containing exactly `a` and
  the elements of `a` .

  Informally: `zfc_ax ⊢ ∀a ∃A ∀x ( x ∈ A ↔ x ∈ a ∨ x = a )`
-/
def successor_ex : zfc_ax ⊢ ∀' ∃' (#0 is_successor_of' #1) :=
begin
  apply separation_proof_scheme' (#0 ∈' #1  ∨' (#0 =' #1)) 1, -- only need to show one direction
  { refl, },
  { apply separation.mem_zfc_ax, },
  { apply allI, -- a
    apply exE ∀' (#0 ∈' #1 ↔' #0 =' #2),
    { -- a ⊢ ∃ A  (A = {a})
      apply allE' _ #0,
      simp only [lift_zfc_ax],
      exact singleton_ex, 
      dsimp, refl, },
    { -- a {a} ⊢ ∃ S ∀ x ( x ∈ a ∨ x = {a} → x ∈ S)
      apply exE ∀'(#0 ∈' #1 ↔' #0 ∈' #3 ∨' #0 ∈' #2),
      { -- a {a} ⊢ ∃ B ( B = a ∪ {a} )
        apply allE' _ #1,
        apply allE' _ #0,
        simp only [lift_zfc_ax],
        apply weak1,
        exact binary_union_ex,
        simp, dsimp, refl },
      { -- a {a} (a ∪ {a}) ⊢ ∃ S ∀ x ( x ∈ a ∨ x = {a} → x ∈ S)
        apply exI #0, -- put `S = a ∪ {a}`
        apply allI,   -- x
        apply impI,   -- assume `x ∈ a ∨ x = a`
        apply orE (#0 ∈' #3) (#0 =' #3),
        { apply hypI1, },
        { -- case `x ∈ a`
          -- a {a} (a ∪ {a}) x ⊢ x ∈ a ∪ {a}
          apply impE (#0 ∈' #3 ∨' #0 ∈' #2),
          { -- a {a} (a ∪ {a}) x ⊢  x ∈ a ∨ x ∈ {a}
            apply orI₁, 
            apply hypI1 },
          { -- a {a} (a ∪ {a}) x ⊢ x ∈ a ∨ x ∈ {a} → x ∈ a ∪ {a}
            apply iffE_l, 
            apply allE_var0,
            apply hypI,
            -- meta
            simp only [set.image_insert_eq],
            right, right, left, refl } },
        { -- case `x = a`
          -- a {a} (a ∪ {a}) x ⊢ x ∈ a ∪ {a} 
          apply impE (#0 ∈' #3 ∨' #0 ∈' #2),
          { -- a {a} (a ∪ {a}) x ⊢  x ∈ a ∨ x ∈ {a}
            apply orI₂, 
            apply impE_insert,
            apply iffE_l,
            apply allE_var0,
            apply hypI,
            -- meta
            simp only [set.image_insert_eq],
            right, right, left, refl },
          { -- a {a} (a ∪ {a}) x ⊢  x ∈ a ∨ x ∈ {a} → x ∈ a ∪ {a}
            apply iffE_l,
            apply allE_var0,
            apply hypI,
            -- meta
            simp only [set.image_insert_eq],
            right, right, left, refl } } } } },
  { dsimp, refl, },
end

/--
  Formal proof that for all sets `a` the successor set `S(a)` exists and is unique.

  Informally: `zfc_ax ⊢ ∀a ∃!A ( A = S(a) )`
-/
def successor_unique_ex : zfc_ax ⊢ ∀' ∃! (#0 is_successor_of' #1) := 
begin
  apply allsI 1,
  apply andI,
  { apply allsE' 1,
    exact successor_ex, },
  { apply extensionality_implies_uniqueness' (#0 ∈' #1  ∨' (#0 =' #1)) (rfl),
    simp only [lift_zfc_ax],
    simp[-extensionality, zfc_ax] },
end

/--
  Formal proof that there exists a set containing exactly the elements common to all inductive sets.

  Informally: `zfc_ax ⊢  ∃A ∀x (x ∈ A ↔ ∀ w (w is inductive → x ∈ w)`
-/
def omega_ex : zfc_ax ⊢ ∃' ∀' ( #0 ∈' #1 ↔' ∀' (#0 is_inductive' →' #1 ∈' #0)) :=
begin
  apply separation_proof_scheme' (∀' (#0 is_inductive' →' #1 ∈' #0)) 0, -- enough to show one direction
  { refl, },
  { apply separation.mem_zfc_ax, },
  { apply exE (#0 is_inductive'),
    { -- ⊢ ∃A ( A is inductive)
      apply hypI,
      exact infinity_ax_mem_zfc_ax }, -- this exists because of the axiom of infinity
    { -- A ⊢ ∃ω ∀x (∀w (w is inductive → w ∈ ω)) → x ∈ ω)
      apply exE ∀'(#0 ∈' #1 ↔' #0 ∈' #2  ∧'  ∀' (#0 is_inductive' →' #1 ∈' #0)),
      { -- A ⊢ ∃B ∀x ( x ∈ B ↔ (x ∈ A) ∧ ∀w (w is inductive → x ∈ w) 
        apply allE_var0,
        apply hypI,
        -- meta
        simp only [lift_zfc_ax],
        right,
        apply separation.mem_zfc_ax (∀'(#0 is_inductive' →' #1 ∈' #0)) 0,
        dsimp, refl },
      { -- B with `∀x ( x ∈ B ↔ ((x ∈ A) ∧ ∀w (w is inductive → x ∈ w)))` 
        -- A B ⊢ ∃ω ∀x  (∀w (w is inductive → x ∈ ω)) → x ∈ ω)
        apply exI #0, -- let `ω := B`
        apply allI,
        apply impI,   -- assume `x` with `(∀w (w is inductive → x ∈ ω))` 
        apply iffE₁ (#0 ∈' #2 ∧' ∀' (#0 is_inductive' →' #1 ∈' #0)),
        { -- A B x ⊢ (x ∈ A ∧ ∀w(w is inductive → x ∈ w)
          apply andI,
          { -- A B x ⊢ x ∈ A 
            apply impE (#2 is_inductive'),
            { -- A B x ⊢ A is inductive 
              apply hypI,
              -- meta
              simp only [set.image_insert_eq],
              right, right, left,
              simp[is_inductive, is_empty, is_successor_of] },
            { -- A B x ⊢  A is inductive → x ∈ A 
              apply allE' _ #2,
              apply hypI,
              -- meta
              left, refl, dsimp, refl } },
          { -- A B x ⊢ ∀w(w is inductive → x ∈ w)
            apply hypI1, } },
        { -- A B x ⊢ x ∈ B ↔ (x ∈ A ∧ ∀w(w is inductive → x ∈ w))
          apply allE_var0,
          apply hypI,
          -- meta
          simp only [set.image_insert_eq],
          right, left, refl } } } },
  { -- meta
    dsimp, refl }
end 

/--
  Formal proof that `ω` exists and is unique. 

  Informally: `zfc_ax ⊢  ∃!A (A = ω)`
-/
def omega_unique_ex : zfc_ax ⊢ ∃! ∀' ( #0 ∈' #1 ↔' ∀' (#0 is_inductive' →' #1 ∈' #0)) :=
begin
  apply andI,
  { exact omega_ex, },
  { apply extensionality_implies_uniqueness' (∀' (#0 is_inductive' →' #1 ∈' #0)) (rfl),
    simp[-extensionality, zfc_ax] },
end

/--
  A formal proof that `ω` is a subset of all inductive sets.

  Informally : `zfc_ax ⊢ ∀ A (A = ω → ∀ w (w is inductive → A ⊆ w))`
-/
def omega_subset_all_inductive : 
  zfc_ax ⊢ ∀' (∀'( #0 ∈' #1 ↔' ∀' (#0 is_inductive' →' #1 ∈' #0)) →' ∀' (#0 is_inductive' →' #1 '⊆ #0) )  :=
begin
  apply allI,
  apply impI,
  apply allI,
  apply impI,
  apply allI,
  apply impI,
  apply impE (#1 is_inductive'),
  { apply hypI, simp only [set.image_insert_eq], right, left, refl },
  { apply allE' _ #1,
    apply iffE₂ ( #0 ∈' #2),
    { apply hypI1, },
    { apply allE_var0,
      apply hypI,
      simp only [set.image_insert_eq], 
      right, right, left, refl },
    { dsimp, refl, } },
end

/--
  A formal proof that `ω` is inductive.

  Informally : `zfc_ax ⊢ ∀ A (A = ω → A is inductive)`
-/
def omega_inductive : zfc_ax ⊢ ∀' (∀'( #0 ∈' #1 ↔' 
  ∀' (#0 is_inductive' →' #1 ∈' #0)) →' (#0 is_inductive')) :=
begin
  apply allI, -- ω
  apply impI, -- assume `ω = { x | ∀ w ( w is inductive → x ∈ w) }`
  apply andI,
  { -- ω ⊢ ∀ x ( x is empty → x ∈ ω)
    apply allI, -- ∅
    apply impI, -- assume `∅ is empty`
    apply iffE₁ ∀'(#0 is_inductive' →' #1 ∈' #0),
    { -- ω ∅ ⊢ ∀ w (w is inductive → ∅ ∈ w)
      apply allI, -- w
      apply impI, -- assume `w is inductive`
      apply impE (#1 is_empty'),
      { -- ω ∅ w ⊢ ∅ is empty
        apply hypI, 
        simp only [set.image_insert_eq], 
        right, left, refl, },
      { -- ω ∅ w ⊢ ∅ is empty → ∅ ∈ w
        apply allE' _ #1,
        apply andE₁,
        apply hypI1,
        unfold is_empty, refl } },
    { -- ω ∅ ⊢ ∅ ∈ ω ↔ ∀ w (w is inductive → ∅ ∈ w)
      apply allE_var0,
      apply hypI,
      simp only[set.image_insert_eq],
      right, left, refl } },
  { -- ω ⊢ ∀ (x ∈ ω → (∀ y ( y = S(x) → y ∈ ω))
    apply allI, -- x
    apply impI, -- assume `x ∈ ω`
    apply allI, -- y
    apply impI, -- assume `y=S(x)`
    apply impE ∀'(#0 is_inductive' →' #1 ∈' #0),
    { -- ω x y ⊢ ∀w (w is inductive → y ∈ w)
      apply allI, -- w
      apply impI, -- assume `w is inductive`
      apply impE (#2 ∈' #0),
      { -- ω x y w ⊢ x ∈ w
        apply impE (#2 ∈' #3),
        { -- ω x y  ⊢ x ∈ ω
          apply hypI, 
          simp only [set.image_insert_eq], 
          right, right, left, refl },
        { -- ω x y w ⊢ x ∈ ω → x ∈ w
          apply allE' (#0 ∈' #4 →' #0 ∈' #1) #2,
          apply impE (#0 is_inductive'),
          { -- ω x y w ⊢ w is inductive 
            apply hypI1 },
          { -- ω x y w ⊢ (w is inductive) → ω ⊆ w
            apply allE_var0,
            apply impE (∀' ( #0 ∈' #4 ↔' ∀' (#0 is_inductive' →' #1 ∈' #0))),
            { -- ω x y w ⊢ ω = ω = { x | ∀ w ( w is inductive → x ∈ w) }
              apply hypI,
              simp only [set.image_insert_eq],
                right, right, right, left, refl },
            { -- ω x y w ⊢ ω = ω = { x | ∀ w ( w is inductive → x ∈ w) } → ((w is inductive) → ω ⊆ w)
              apply allE' _ #3,
              apply weak zfc_ax,
              exact omega_subset_all_inductive,
              simp only [set.image_insert_eq, lift_zfc_ax],  
              assume y yh, simp[yh],
              unfold is_inductive, 
              refl, } }, 
            refl }, },
      { -- ω x y w ⊢ x ∈ w → y ∈ w
        apply impI, -- assume `x ∈ w`
        apply impE (#1 is_successor_of' #2),
        { -- ω x y w ⊢ y = S(x)
          apply hypI, 
          simp only [set.image_insert_eq],
          right, right, left, 
          dsimp[is_successor_of], refl },
        { -- ω x y w ⊢ y = S(x) → y ∈ w
          apply allE' _ #1,
          apply impE (#2 ∈' #0),
          { -- ω x y w ⊢ x ∈ w
            apply hypI1, },
          { -- ω x y w ⊢ x ∈ w → (∀ y ( y = S(x) → y ∈ w))
            apply allE' _ #2,
            apply andE₂, 
            apply hypI, 
            simp only[set.image_insert_eq],
            right, left, refl,
            unfold is_successor_of, refl },
        { unfold is_successor_of, 
          refl } } } },
    { -- ω x y ⊢ ∀w (w is inductive → y ∈ w) → y ∈ ω
      apply iffE_l,
      apply allE_var0,
      apply hypI,
      simp only [set.image_insert_eq],
      right, right, left, refl } },
end

/--
  A formal proof that `ω` is the smallest inductive set.

  Informally : 
  `zfc_ax ⊢ ∀ X ( A = ω → (A is inductive ∧ ∀ w (w is inductive → X ⊆ w))`
-/
def omega_smallest_inductive : 
  zfc_ax ⊢ ∀' ( ∀'( #0 ∈' #1 ↔' ∀' (#0 is_inductive' →' #1 ∈' #0)) 
                    →' ((#0 is_inductive') ∧' ∀'((#0 is_inductive') →' #1 '⊆ #0))) :=
begin
  apply allI, -- ω
  apply impI, -- ω = { x | ∀ w ( w is inductive → x ∈ w) }
  apply andI,
  { -- ω ⊢ ω is inductive 
    apply impE_insert,
    apply allE_var0,
    simp only [lift_zfc_ax],
    apply omega_inductive
  },
  { -- ω ⊢ ∀ w (w is inductive → ω ⊆ w)
    apply impE_insert,
    apply allE_var0,
    simp only [lift_zfc_ax],
    apply omega_subset_all_inductive },
end

end zfc_proofs

/--
  Main Theorem: ZFC proves that `ω` is the smallest inductive set.
-/
theorem omega_smallest_inductive_provable_within_zfc :
 ∀' ( ∀'( #0 ∈' #1 ↔' ∀' (#0 is_inductive' →' #1 ∈' #0)) 
      →' ((#0 is_inductive') ∧' ∀'((#0 is_inductive') →' #1 '⊆ #0))) is_provable_within zfc_ax :=
begin use omega_smallest_inductive, end

end zfc