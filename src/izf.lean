import fol
import data.set

/-!
# IZF set theory

In this file we define the signature and axioms of intuitionistic Zermelo-Fraenkel set theory
and give a natural deduction proof of the induction principle in its set theoretical form.

We also briefly discuss how statements about named variables like 
  "φ is a formula with B not free"
in the formulation of the axiom schemes of separation and collection
can be translated to De Bruijn variables using lifts.

## Main results

- `omega_smallest_inductive_provable_within_izf`: 
    we show that ZFC proves that ω is the smallest inductive set. a direct consequence of
- `omega_smallest_inductive`: 
    a natural deduction proof that ω is the smallest inductive set

## References
* [P. Aczel, M. Rathjen, *Notes on Constructive Set Theory*] [AR01]
  -- for the axioms of IZF
* [L. Crosilla, *Set Theory: Constructive and Intuitionistic ZF*] [LC20]
  -- for cross referencing
-/


namespace izf
open fol
universe variable u

section izf_signature

-- pp notation for inserting elements into a data.set
local infix ` >> ` := insert

/- We will use single predicate for membership -/
inductive pred_symb : ℕ → Type u
| elem : pred_symb 2
--| subset : pred_symb 2

/- We allow constants for the empty set and ω,
  unary function symbols for the union set and the powerset
  and a binary function symbol for the pair set -/
inductive func_symb : ℕ → Type u
| empty : func_symb 0
| omega : func_symb 0
| union : func_symb 1
| power : func_symb 1
| pair  : func_symb 2
--| succ  : func_symb 1
 
def 𝒮 : signature := { func_symb:= izf.func_symb , pred_symb:= izf.pred_symb }

-- Definitions and notations for our functions
@[simp]def emptyset                 : term 𝒮 := (func func_symb.empty : term 𝒮)
@[simp]def omegaset                 : term 𝒮 := (func func_symb.omega : term 𝒮)
@[simp]def unionset (t : term 𝒮)    : term 𝒮 :=  fapp (func func_symb.union) t
@[simp]def powerset (t : term 𝒮)    : term 𝒮 := fapp (func func_symb.power) t
@[simp]def pairset (t₁ t₂ : term 𝒮) : term 𝒮 := fapp (fapp (func func_symb.pair) t₁) t₂
--def successorset (t: term 𝒮) : term 𝒮 :=  fapp (func func_symb.succ) t

notation `⌀`  := emptyset -- this is not ∅; type ⌀ using \diameter
notation `ω`  := omegaset
prefix ⋃      := unionset
prefix 𝒫      := powerset
--prefix S:max := successorset
notation ⦃ a ` , ` b ⦄ := pairset a b  -- type ⦃ and ⦄ using \{{ and \}}
notation ⦃ a ⦄ := pairset a a

-- Definition and notation for our predicate
@[simp] def memb (t₁ t₂: term 𝒮): formula 𝒮 := papp (papp (pred pred_symb.elem) t₁) t₂
infix ` ∈' `:100 := memb

-- Meta predicates and functions
-- def subset (t₁ t₂: term 𝒮): formula 𝒮 := papp (papp (pred_symb pred_symb.subset) t₁) t₂
@[simp] def subset (t₁ t₂: term 𝒮): formula 𝒮 := ∀'( #0 ∈' (t₁ ↑ 1 ＠  0) →' #0 ∈' (t₂ ↑ 1 ＠  0))
infix ` ⊆' `:100 := subset

@[simp] def successor_set (t: term 𝒮) : term 𝒮 := ⋃⦃ t , ⦃ t ⦄ ⦄
prefix `S`:max := successor_set

@[simp] def is_inductive (t : term 𝒮) 
  := ⌀ ∈' t ∧' ∀' (#0 ∈' (t ↑ 1 ＠  0) →' S #0 ∈' (t ↑ 1 ＠  0))
postfix ` is_inductive`:max := is_inductive

@[simp] def unique_in_var0 (φ: formula 𝒮) : formula 𝒮 
  :=  ∀' ∀' ((φ ↑ 1 ＠ 1 ) ∧' (φ ↑ 1 ＠ 0) →' (#0 =' #1) )

@[simp] def unique_ex (φ : formula 𝒮) : formula 𝒮 
  := (∃'φ) ∧' (unique_in_var0 φ)
prefix `∃!`:110 := unique_ex 

end izf_signature

-- reducing terms helps with evaluating lifts and substitutions
-- however, pred_symb and func_symb will make more difficult:                        
-- #reduce (⌀ ∈' ω  ∧' ⦃ ⌀, S⦃ #3 ⦄ ⦄ ∈' 𝒫#1) ↑ 1 ＠ 1                   
/-
((pred pred_symb.elem).papp (func func_symb.empty)).papp (func func_symb.omega) ∧'
  ((pred pred_symb.elem).papp
     (((func func_symb.pair).fapp (func func_symb.empty)).fapp
        ((func func_symb.union).fapp
           (((func func_symb.pair).fapp (((func func_symb.pair).fapp #4).fapp #4)).fapp
              (((func func_symb.pair).fapp (((func func_symb.pair).fapp #4).fapp #4)).fapp
                 (((func func_symb.pair).fapp #4).fapp #4)))))).papp
    ((func func_symb.power).fapp #2)
-/

-- this seems helps pretty printing reduced terms and formulas and makes them much easier to read
notation `'⌀` := func func_symb.empty
notation `'ω` := func func_symb.omega
notation `'⋃` t :=  fapp (func func_symb.union) t
notation `'𝒫` t := fapp (func func_symb.power) t 
--notation `'S` t := fapp (func func_symb.succ) t
notation `'{ ` a ` , `b` }` := fapp (fapp (func func_symb.pair) a) b
notation s ` '∈ `:100 t := papp (papp (pred pred_symb.elem) s) t
notation s ` '⊆ `:100 t := papp (papp (pred pred_symb.subset) s) t

-- after
-- #reduce (⌀ ∈' ω  ∧' ⦃ ⌀, S⦃ #3 ⦄ ⦄∈' 𝒫#1) ↑ 1 ＠ 1      
/-
  ('⌀ '∈ 'ω) ∧' '{ '⌀ , '⋃'{ '{ #4 , #4 } , '{ '{ #4 , #4 } , '{ #4 , #4 } } } } '∈ '𝒫#2
-/
-- much better

section izf_axioms

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


namespace collection
/-
  The collection axiom scheme is defined as the closure of
    `∀A ( ∀x(x ∈ A → ∃y φ) → ∃B ∀x (x ∈ A →  ∃y (y ∈ B ∧ φ)` (1)
  for all formulas φ such that B is not free in φ.
  Observe that in this case the the quantifier before B binds variables pointing to 2.
  Thus the side condition can be stated as
    `φ = ψ ↑ 1 ＠ 2` 
  for a formula `ψ` and we obtain our axiom scheme as the closure of the formula below.
-/
@[simp] def formula (φ: formula 𝒮) := 
  (∀'( ∀'(#0 ∈' #1 →' ∃'φ) →' ( ∃' ∀' ( #0 ∈' #2 →' (∃' (#0 ∈' #2 ∧' (φ ↑ 1 ＠ 2))))))) 
/-
  To define the closure of (1) we usually state collection in terms of formulas φ(x, y, A, x₁, ... , xₙ)
  with free variables among (but not necessarily exactly) x, y, A, x₁, ... , xₙ.

  This then translates to `φ_h: closed (n+3) φ` and we can proceed as in the case of separation.
-/
lemma closed  {φ} {k} (H: closed (k+3) φ) : closed k (formula φ) :=
begin
  have : ¬ k+4 ≤ 2, by linarith,
  have : ¬ k+3 ≤ 2, by linarith,
  have h₁ : 0 ≤ k+3, from (k+3).zero_le,
  have h₂ : 1 ≤ k+3, by linarith,
  have h₃ : 2 ≤ k+3, by linarith,
  have H₁ : (φ ↑ 1 ＠ 0) ↑ 1 ＠ (k + 4) = φ ↑ 1 ＠ 0,
    begin rw ←(lift_lift φ 1 1 h₁), congr, exact H, end,
  have H₂ : (φ ↑ 1 ＠ 1) ↑ 1 ＠ (k + 4) = φ ↑ 1 ＠ 1,
    begin rw ←(lift_lift φ 1 1 h₂), congr, exact H, end,
  have H₃ : (φ ↑ 1 ＠ 2) ↑ 1 ＠ (k + 4) = φ ↑ 1 ＠ 2,
    begin rw ←(lift_lift φ 1 1 h₃), congr, exact H, end,
  rw closed at H, clear h₂,
  simp[*, closed],
end 

def sentence  (φ : fol.formula 𝒮) {k : ℕ} (H: formula.closed (k+3) φ) : fol.formula 𝒮 
  := formula.closure (formula φ) (closed H)

lemma is_sentence  (φ : fol.formula 𝒮) {k : ℕ} (H: fol.formula.closed (k+3) φ) :
  (sentence φ H) is_sentence' := begin exact closure_is_sentence (closed H) end

/- To following definition and lemmas are used to make future proofs more explicit and readable. -/
lemma mem {Γ:set $ fol.formula 𝒮} {ψ} {k} (φ) (φ_h: formula.closed (k+3) φ) 
  (h : ψ = sentence φ φ_h) (H: (sentence φ φ_h) ∈ Γ) : ψ ∈ Γ :=
begin subst h, exact H end 

def scheme : set $ fol.formula 𝒮 := 
  { (sentence φ φ_h) |  (φ : fol.formula 𝒮) (k: ℕ) (φ_h : fol.formula.closed (k+3) φ) }

lemma mem_scheme (φ : fol.formula 𝒮) {k : ℕ} (φ_h: fol.formula.closed (k+3) φ)
  : sentence φ φ_h ∈ scheme := begin existsi [φ, k, φ_h], refl, end

end collection

namespace set_induction
/-
  The set induction axiom scheme is defined as the closure of
    `∀A (∀x (x ∈ A → φ(x)) → φ) → ∀A φ` (1)
  for all formulas φ.
-/
@[simp] def formula (φ: formula 𝒮) := 
  (∀'(∀'(#0 ∈' #1 →' (φ ↑ 1 ＠ 1)) →' φ ) →' (∀'φ))

/-
  To define the closure of (1) we usually state collection in terms of formulas φ( A, x₁, ... , xₙ)
  with free variables among (but not necessarily exactly) A, x₁, ... , xₙ.

  This then translates to `φ_h: closed (n+1) φ` and we can proceed as in the case of separation.
-/
lemma closed  {φ} {n} (φ_h: closed (n+1) φ) : closed n (formula φ) :=
begin
  have : φ ↑ 1 ＠ 1 ↑ 1 ＠ (n + 1 + 1) = φ ↑ 1 ＠ 1 :=
  begin rw ←(lift_lift φ 1 1 (nat.succ_pos n)), congr, exact φ_h, end,
  rw closed at φ_h,
  simp*,
end 

def sentence  (φ : fol.formula 𝒮) {n : ℕ} (φ_h: formula.closed (n+1) φ) : fol.formula 𝒮 
  := formula.closure (formula φ) (closed φ_h)

lemma is_sentence  (φ : fol.formula 𝒮) {n : ℕ} (φ_h: fol.formula.closed (n+1) φ) :
  (sentence φ φ_h) is_sentence' := begin exact closure_is_sentence (closed φ_h) end

/- To following definition and lemmas are used to make future proofs more explicit and readable. -/
lemma mem {Γ:set $ fol.formula 𝒮} {ψ} (φ) {n} (φ_h: formula.closed (n+1) φ) 
  (h : ψ = sentence φ φ_h) (H: (sentence φ φ_h) ∈ Γ) : ψ ∈ Γ :=
begin subst h, exact H end 

def scheme : set $ fol.formula 𝒮 := 
  { (sentence φ φ_h) |  (φ : fol.formula 𝒮) (k: ℕ) (φ_h : fol.formula.closed (k+1) φ) }

lemma mem_scheme (φ : fol.formula 𝒮) {k : ℕ} (φ_h: fol.formula.closed (k+1) φ)
  : sentence φ φ_h ∈ scheme := begin existsi [φ, k, φ_h], refl, end

end set_induction


/- ∀b ∀a (∀x (x ∈ a ↔ x ∈ b) → a = b) -/
@[simp] def extensionality : formula 𝒮 := ∀' ∀' ( (∀' (#0 ∈' #1 ↔' #0 ∈' #2)) →' (#0 =' #1) )
/- ∀x ( x ∈ ⌀ ↔ x ≠ x) -/
@[simp] def emptyset_ax    : formula 𝒮 := ∀' (#0 ∈' ⌀ ↔' ¬'(#0 =' #0) )
/- ∀b ∀a ∀x (x ∈{a,b} ↔ x = a ∨ x = b) -/
@[simp] def pairset_ax     : formula 𝒮 := ∀' ∀' ∀' ( #0 ∈' ⦃ #1 , #2 ⦄ ↔' (#0 =' #1 ∨' #0 =' #2))
/- ∀F ∀x (x ∈ ⋃F ↔ ∃y (x ∈ y ∧ y ∈ x))  -/
@[simp] def unionset_ax    : formula 𝒮 := ∀' ∀' ( #0 ∈' ⋃#1 ↔' ∃'( #1 ∈' #0 ∧' #0 ∈' #2))
/- ∀y ∀x (x ∈ 𝒫(y) → x ⊆ y) -/
@[simp] def powerset_ax    : formula 𝒮 := ∀' ∀' (#0 ∈' 𝒫#1 ↔' #0 ⊆' #1)
/- ∀x ( x ∈ ω ↔ ∀w (w is inductive → x ∈ w)) -/
@[simp] def omega_ax       : formula 𝒮 := ∀' (#0 ∈' ω ↔' ∀'( (#0 is_inductive) →' #1 ∈' #0))
/- ∀xₙ ... ∀x₁ ∀A (∀x (x ∈ A → φ(x)) → φ(A)) → ∀A φ(A) -/
@[simp] def set_induction_ax  (φ : formula 𝒮) {n : ℕ} (φ_h: closed (n+1) φ) : formula 𝒮  
  := set_induction.sentence φ φ_h
/-- ∀xₙ ... ∀x₁ ∀A ∃B ∀x ( x ∈ B ↔ x ∈ A ∧ φ ↑ 1 ＠ 1) -/
@[simp] def separation_ax  (φ : formula 𝒮) {n: ℕ} (φ_h: closed (n+2) φ) : formula 𝒮 
  := separation.sentence φ φ_h
/-- ∀xₙ ... ∀x₁ ∀A ( ∀x(x ∈ A → ∃y φ) → ∃B ∀x (x ∈ A →  ∃y (y ∈ B ∧ φ) -/
@[simp] def collection_ax (φ : formula 𝒮) {n : ℕ} (φ_h: closed (n+3) φ) : formula 𝒮 
  := collection.sentence φ φ_h

-- optional: definition of the subset predicate
-- @[simp] def subset_def   : formula 𝒮 := ∀' ∀' ( #0 ⊆' #1  ↔' ∀' (#0 ∈' #1 →' #0 ∈' #2) )

/-
 * The following lemmas provide a convenient way to make explicit which axioms are used inside our proofs.
 * For separation and collection we can use separation.mem and collection.mem respectively.
-/
lemma extensionality_mem {Γ: set $ formula 𝒮}{φ}(h: φ = extensionality)(H: extensionality ∈ Γ) : φ ∈ Γ :=
begin subst h, exact H end
lemma emptyset_ax_mem {Γ: set $ formula 𝒮} {φ} (h: φ = emptyset_ax) (H: emptyset_ax ∈ Γ)  : φ ∈ Γ :=
begin subst h, exact H end
lemma pairset_ax_mem {Γ: set $ formula 𝒮} {φ} (h: φ = pairset_ax) (H: pairset_ax ∈ Γ)  : φ ∈ Γ :=
begin subst h, exact H end
lemma unionset_ax_mem {Γ: set $ formula 𝒮} {φ} (h: φ = unionset_ax) (H: unionset_ax ∈ Γ)  : φ ∈ Γ :=
begin subst h, exact H end
lemma powerset_ax_mem {Γ: set $ formula 𝒮} {φ} (H: powerset_ax ∈ Γ) (h: φ = powerset_ax) : φ ∈ Γ :=
begin subst h, exact H end
lemma omega_ax_mem {Γ: set $ formula 𝒮} {φ} (h: φ = omega_ax) (H: omega_ax ∈ Γ) : φ ∈ Γ :=
begin subst h, exact H end


/--
  The set of axioms for IZF.
-/
def izf_ax : set $ formula 𝒮 := { extensionality, emptyset_ax, pairset_ax, 
                                  unionset_ax, powerset_ax, omega_ax } 
                                  ∪ set_induction.scheme
                                  ∪ separation.scheme
                                  ∪ collection.scheme

lemma izf_ax_set_of_sentences : ∀ ϕ ∈ izf_ax , sentence ϕ :=
begin
  intros φ h,
  repeat {cases h,};
  try {unfold sentence closed, refl, },
  all_goals { cases h_h with k H,
              cases H with ϕ_closed,
              subst H_h },
  exact set_induction.is_sentence _ ϕ_closed,
  exact separation.is_sentence _ ϕ_closed,
  exact collection.is_sentence _ ϕ_closed,
end

lemma lift_izf_ax {m i : ℕ}: (λ (ϕ: formula 𝒮) , ϕ ↑ m ＠ i) '' izf_ax = izf_ax 
  := lift_set_of_sentences_id izf_ax_set_of_sentences

end izf_axioms


section izf_proofs

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
  Proof scheme. Provides a formal oroof of `∃B ∀x(x ∈ B ↔ φ)`
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
  Formal proof showing that `{a} := {a,a}` satisfies the defining property of the singleton set, 
  derived from the pairset axiom.

  Informally: `{pairset_ax} ⊢ ∀ a : {a} = { x | x = a }`.
-/
def singleton_def: {pairset_ax} ⊢ ∀' ∀' (#0 ∈' ⦃ #1 ⦄ ↔' #0 =' #1) :=
begin
  apply allI, -- a
  apply allI, -- x
  apply andI,
  { -- a x ⊢ x ∈ {a} → x = a
    apply impI, -- assume `x ∈ {a}`
    apply orE (#0 =' #1) (#0 =' #1),
    { -- a x ⊢ x = a ∨ x = a 
      apply impE_insert,
      apply iffE_r,
      apply allE_var0,
      apply allE' _ #1,
      apply allE' _ #1,
      apply hypI,
      -- meta
      apply pairset_ax_mem (rfl),
      all_goals {simp [set.image_singleton] } },
    { -- assume x = a
      -- a x ⊢  x = a
      apply hypI1 },
    { -- assume x = a
      -- a x ⊢  x = a
      apply hypI1 },
  },
  { -- a x ⊢ x = a → x ∈ {a}
    apply impI, -- assume `x = a`
    apply impE (#0 =' #1 ∨' #0 =' #1),
    { -- a x ⊢ x = a ∨ x = a 
      apply orI₁, 
      apply hypI1, },
    { -- a x ⊢ (x = a ∨ x = a ) → x ∈ {a}
      apply iffE_l, 
      apply allE_var0,
      apply allE' _ #1,
      apply allE' _ #1,
      apply hypI,
      -- meta
      apply pairset_ax_mem (rfl),
      all_goals {simp [set.image_singleton] } } }
end

/--
  Informally: `Γ ⊢ φ` provided `φ = ∀ a : { a } = { x | x = a }`
  and `pairset_ax ∈ Γ`.
-/
def singleton_def' {Γ} {φ : formula 𝒮} (h₁: φ = ∀' ∀' (#0 ∈' ⦃ #1 ⦄ ↔' #0 =' #1)) (h₂ : pairset_ax ∈ Γ ) :
  Γ ⊢ φ  :=
begin
  subst h₁,
  apply weak_singleton pairset_ax,
  apply singleton_def,
  assumption,
end

/--
  A formal proof showing that `a ∪ b := ⋃{a,b}` satisfies the defining property of the binary union,
  derived from the pairset and unionset axioms.

  Informally: `{pairset_ax, unionset_ax} ⊢ ∀b ∀a : a ∪ b = { x | x ∈ a ∨ x ∈ b }`.
-/
def binary_union_def : {pairset_ax, unionset_ax} ⊢ ∀' ∀' ∀' (#0 ∈' ⋃ ⦃ #1, #2 ⦄ ↔' #0 ∈' #1 ∨' #0 ∈' #2) :=
begin
  apply allI, -- b
  apply allI, -- a
  apply allI, -- x
  apply andI,
  { -- b a x ⊢ x ∈ a ∪ b → x ∈ a ∨ x ∈ b
    apply impI,  -- assume `x ∈ a ∪ b`
    apply exE (#1 ∈' #0 ∧' #0 ∈' ⦃#2 , #3⦄), -- y with `x ∈ y ∧ y ∈ {a,b}`
    { -- b a x ⊢ ∃y (x ∈ y ∧ y ∈ {a,b})
      apply impE_insert, 
      apply iffE_r, 
      apply allE' _ #0,
      apply allE' _ ⦃#1 , #2⦄,
      apply hypI,
      -- meta
      apply unionset_ax_mem (rfl),
      all_goals { try { simp[set.image_insert_eq], }, },
      split; refl },
    { -- b a x y ⊢ x ∈ a ∨ x ∈ b
      apply impE (#0 =' #2 ∨' #0 =' #3),
      { -- b a x y ⊢ y = a ∨ y = b
        apply impE (#0 ∈'  ⦃#2 , #3⦄ ),
        { -- b a x y ⊢ y ∈ {a,b}
          apply andE₂, 
          apply hypI1 },
        { -- b a x y ⊢ y ∈ {a,b} →  y = a ∨ y = b
          apply iffE_r ,
          apply allE' _ #0,
          apply allE' _ #2,
          apply allE' _ #3,
          apply hypI,
          -- meta
          apply pairset_ax_mem (rfl),
          all_goals { try { simp[set.image_insert_eq] } },
          split; refl } },
      { -- b a x y ⊢ y = a ∨ y = b → x ∈ a ∨ x ∈ b 
        apply impI, -- assume `y = a ∨ y = b`
        apply orE (#0 =' #2) (#0 =' #3),
        { -- b a x y ⊢ y = a ∨ y = b
          apply hypI1, },
        { -- assume `y = a`
          -- b a x y ⊢ x ∈ a ∨ x ∈ b
          apply orI₁,
          apply eqE' #0 #2 (#2 ∈' #0),
          { -- b a x y ⊢ y = a
            apply hypI1, },
          { -- b a x y ⊢ x ∈ y
            apply andE₁,
            apply hypI, 
            simp[set.image_insert_eq] },
          { refl } },
        { -- assume `y = b`
          -- b a x y ⊢ x ∈ a ∨ x ∈ b
          apply orI₂,
          apply eqE' #0 #3 (#2 ∈' #0),
          { -- b a x y ⊢ y = b
            apply hypI1, },
          { -- b a x y ⊢ x ∈ y
            apply andE₁,
            apply hypI, 
            simp[set.image_insert_eq] },
          { refl } } } } },
  { -- b a x ⊢ (x ∈ a ∨ x ∈ b) → x ∈ a ∪ b
    apply impI, -- assume `(x ∈ a) ∨ (x ∈ b)`
    apply orE (#0 ∈' #1)  (#0 ∈' #2),
    { -- b a x ⊢ (x ∈ a) ∨ (x ∈ b)
      apply hypI1 },
    { -- assume `x ∈ a`
      -- b a x ⊢ x ∈ a ∪ b
      apply impE (∃'(#1 ∈' #0 ∧' #0 ∈'  ⦃#2 , #3⦄)),
      { -- b a x ⊢ ∃y (x ∈ y ∧ y ∈ {a,b})
        apply exI #1, 
        apply andI,
        { -- b a x ⊢ x ∈ a
          apply hypI1, },
        { -- b a x ⊢ a ∈ {a,b}
          apply impE (#1 =' #1 ∨' #1 =' #2),
          { -- b a x ⊢ (a = a ∨ a = b)
            apply orI₁, 
            apply eqI, },
          { -- b a x ⊢ (a = a ∨ a = b) → a ∈ {a,b}
            apply iffE_l,
            apply allE' _ #1,
            apply allE' _ #1,
            apply allE' _ #2,
            apply hypI,
            apply pairset_ax_mem (rfl),
            all_goals { try { simp[set.image_insert_eq], }, },
            split; refl } } },
      { -- b a x ⊢ ∃y ( x ∈ y ∧ y ∈ {a,b}) → x ∈ a ∪ b
        apply iffE_l ,
        apply allE_var0,
        apply allE' _ ⦃ #1 , #2 ⦄,
        apply hypI,
        apply unionset_ax_mem (rfl),
        all_goals{ simp[set.image_insert_eq] },
        refl } },
    { -- assume `x ∈ b`
      -- b a x ⊢ x ∈ a ∪ b
      apply impE (∃'(#1 ∈' #0 ∧' #0 ∈' ⦃#2 , #3⦄)),
      { -- b a x ⊢ ∃y (x ∈ y ∧ y ∈ {a,b})
        apply exI #2, 
        apply andI,
        { -- b a x ⊢ x ∈ b
          apply hypI1, },
        { -- b a x ⊢ b ∈ {a,b}
          apply impE (#2 =' #1 ∨' #2 =' #2),
          { -- b a x ⊢ (b = a ∨ b = b)
            apply orI₂, 
            apply eqI, },
          { -- b a x ⊢ (b = a ∨ b = b) → a ∈ {a,b}
            apply andE₂ _,
            apply allE' _ #2,
            apply allE' _ #1,
            apply allE' _ #2,
            apply hypI,
            apply pairset_ax_mem (rfl),
            all_goals { try { simp[set.image_insert_eq], }, },
            split; refl } } },
      { -- b a x ⊢ ∃y ( x ∈ y ∧ y ∈ {a,b}) → x ∈ a ∪ b
        apply iffE_l ,
        apply allE_var0,
        apply allE' _ ⦃ #1 , #2 ⦄,
        apply hypI,
        apply unionset_ax_mem (rfl),
        all_goals { simp[set.image_insert_eq] },
        refl } } }
end

/--
  Informally: `Γ ⊢ φ` provided `φ =  ∀ b ∀ a : a ∪ b = { x | x ∈ a ∨ x ∈ b }`
  and `pairset_ax, unionset_ax ∈ Γ`.
-/
def binary_union_def' {Γ} {φ : formula 𝒮} (h₁: φ = ∀' ∀' ∀'(#0 ∈' ⋃ ⦃ #1, #2 ⦄ ↔' #0 ∈' #1 ∨' #0 ∈' #2) )
  (h₂: pairset_ax ∈ Γ ) (h₃ : unionset_ax ∈ Γ) : Γ  ⊢ φ :=
begin
  subst h₁,
  apply weak {pairset_ax, unionset_ax},
  apply binary_union_def,
  intros x h,
  cases h,
  { subst h,
    exact h₂ },
  { rw set.mem_singleton_iff at h,
    subst h,
    exact h₃ }
end

/--
  A formal proof showing that `S(a) := a ∪ {a}` satisfies the defining property of the successor set, 
  derived from the pairset and unionset axioms.

  Informally: `{pairset_ax, unionset_ax} ⊢  ∀a : S(a) = { x | x ∈ a ∨ x = a }`.
-/
def successor_def : {pairset_ax, unionset_ax} ⊢ ∀' ∀' (#0 ∈' S#1 ↔' #0 ∈' #1 ∨' #0 =' #1) :=
begin
  apply allI, -- a
  apply allI, -- x
  apply andI,
  { -- a x ⊢ x ∈ S(a) → x ∈ a ∨ x = a  
    apply impI, -- assume `x ∈ S(a)`
    apply impE (#0 ∈' #1 ∨' #0 ∈' ⦃ #1 ⦄),
    { -- a x ⊢ x ∈ a ∨ x ∈ {a}
      apply impE (#0 ∈' S#1),
      { -- a x ⊢ x ∈ S(a)
        apply hypI1, },
      { -- a x ⊢ x ∈ S(a) → x ∈ a ∨ x ∈ {a}
        apply iffE_r,
        apply allE_var0,
        apply allE' _ #1,
        apply allE' _ ⦃ #1 ⦄,
        apply binary_union_def' (rfl),
        all_goals{ simp[set.image_insert_eq] } } },
    { -- a x ⊢ x ∈ a ∨ x ∈ {a} → x ∈ a ∨ x = a
      apply impI, -- assume `x ∈ a ∨ x ∈ {a}`
      apply orE (#0 ∈' #1) ( #0 ∈' ⦃ #1 ⦄),
      { -- a x ⊢ x ∈ a ∨ x ∈ {a}
        apply hypI1, },
      { -- assume `x ∈ a`
        -- a x ⊢ x ∈ a ∨ x = a 
        apply orI₁,
        apply hypI1 },
      { -- assume `x ∈ {a}`
        -- a x ⊢ x ∈ a ∨ x = a  
        apply orI₂,
        apply impE_insert,
        apply iffE_r,
        apply allE_var0,
        apply allE' _ #1,
        apply singleton_def' (rfl),
        all_goals{ simp[set.image_insert_eq] } } } },
  { -- a x ⊢ x ∈ a ∨ x = a → x ∈ S(a)
    apply impI, -- assume `x ∈ a ∨ x = a`
    apply orE (#0 ∈' #1) (#0 =' #1),
    { -- a x ⊢ x ∈ a ∨ x = a
      apply hypI1, },
    { -- assume `x ∈ a`
      -- a x ⊢ x ∈ S(a)
      apply impE (#0 ∈' #1 ∨' #0 ∈' ⦃ #1 ⦄),
      { -- a x ⊢ x ∈ a ∨ x ∈ {a}
        apply orI₁, 
        apply hypI1,},
      { -- a x ⊢ x ∈ a ∨ x ∈ {a} → x ∈ S(a)
        apply iffE_l, 
        apply allE' _ #0,
        apply allE' _ #1,
        apply allE' _ ⦃ #1 ⦄, 
        apply binary_union_def' (rfl),
        all_goals{ simp[set.image_insert_eq] } } },
    { -- assume `x = a`
      -- a x ⊢ x ∈ S(a)
      apply impE (#0 ∈' #1 ∨' #0 ∈' ⦃ #1 ⦄),
      { -- a x ⊢ x ∈ a ∨ x ∈ {a}
        apply orI₂, 
        apply impE_insert,
        apply iffE_l,
        apply allE' _ #0,
        apply allE' _ #1,
        apply singleton_def' (rfl),
        all_goals{ simp[set.image_insert_eq] } },
      { -- a x ⊢ x ∈ a ∨ x ∈ {a} → x ∈ S(a)
        apply iffE_l,
        apply allE' _ #0,
        apply allE' _ #1,
        apply allE' _ ⦃ #1 ⦄,
        apply binary_union_def' (rfl),
        all_goals{ simp[set.image_insert_eq] } } } }
end


/--
  Formal proof that there (trivially) exists a set 
  containing exactly the elements common to all inductive sets
  and that such a set is unique,
  derived from the omega axiom and extensionality.

  Informally: `{omega_ax, extensionality} ⊢ ∃! w₀ : w₀ = { x | ∀ w : (w is inductive) →  x ∈ w }`.
-/
def omega_unique 
  : {omega_ax, extensionality} ⊢ ∃! ∀' (#0 ∈' #1 ↔' ∀'( (#0 is_inductive) →' #1 ∈' #0)) := 
begin
  apply andI,
  { -- ∃ case is trivial
    apply exI ω,
    apply hypI,
    simp },
  { -- uniqueness
    apply extensionality_implies_uniqueness' (∀'(#0 is_inductive →' #1 ∈' #0)) (rfl),
    simp }
end

/--
  A formal proof that `ω` is a subset of all inductive sets,
  derived from the omega axiom.

  Informally: `{omega_ax} ⊢ ∀ w : (w is inductive) →  ω ⊆ w`.
-/
def omega_subset_all_inductive: 
  {omega_ax} ⊢  ∀' (#0 is_inductive →' (ω ⊆' #0))   :=
begin
  apply allI, -- w
  apply impI, -- assume `w is inductive`
  apply allI, -- x 
  apply impI, -- assume `x ∈ ω`
  apply impE (#1 is_inductive),
  { -- w x ⊢ w is inductive
    apply hypI, 
    simp [set.image_insert_eq] },
  { -- w x ⊢ (w is inductive) → x ∈ w 
    apply allE' (#0 is_inductive →' #1 ∈' (#0)) #1,
    apply iffE₂ (#0 ∈' ω),
    { -- w x ⊢ x ∈ ω
      apply hypI1 },
    { -- w x ⊢ x ∈ ω ↔ ∀ w ((w is inductive) → x ∈ w) 
      apply allE_var0,
      apply hypI,
      apply omega_ax_mem,
      all_goals {simp[set.image_insert_eq] } },
    { refl } }
end

/--
  Informally: `Γ ⊢ ∀ w : (w is inductive) →  ω ⊆ w`, provided `omega_ax ∈ Γ`.
-/
def omega_subset_all_inductive' {Γ} (h: omega_ax ∈ Γ) : 
  Γ ⊢  ∀' (#0 is_inductive →' (ω ⊆' #0))   :=
begin
  apply weak {omega_ax},
  exact omega_subset_all_inductive,
  exact set.singleton_subset_iff.mpr h,
end

/-- 
  A formal proof of `ω is inductive`, derived from the omega axiom. 
-/
def omega_inductive : {omega_ax} ⊢ ω is_inductive :=
begin
  apply andI,
  { -- ⊢ ⌀ ∈ ω
    apply impE ∀'(#0 is_inductive →' ⌀ ∈' #0), 
    { -- ⊢ ∀ w ( w is inductive → ⌀ ∈ w)
      apply allI,
      apply impI,
      apply andE₁,
      apply hypI,
      simp },
    { -- ⊢ ∀ w ( w is inductive → ⌀ ∈ w) → ⌀ ∈ ω
      apply iffE_l,
      apply allE' _ ⌀,
      apply hypI,
      apply omega_ax_mem (rfl),
      all_goals { simp } } },
  { -- ⊢ ∀ x ( x ∈ ω → S(x) ∈ ω)
    apply allI, -- x
    apply impI, -- assume `x ∈ ω`
    apply impE (∀'(#0 is_inductive →' S#1 ∈' #0)),
    { -- x  ⊢ ∀ w ( (w is inductive) → S(x) ∈ w)
      apply allI, -- w
      apply impI, -- assume `w is inductive`
      apply impE (#1 ∈' #0),
      { -- x w ⊢ x ∈ w
        apply impE (#1 ∈' ω),
        { -- x w ⊢ x ∈ ω
          apply hypI,
          simp[set.image_insert_eq] },
        { -- x w ⊢ x ∈ ω → x ∈ w
          apply allE' (#0 ∈' ω →' #0 ∈' #1) #1,
          apply impE_insert,
          apply allE_var0,
          apply omega_subset_all_inductive',
          { simp [set.image_insert_eq] },
          { refl } } },
      { -- (x ∈ ω) (w is inductive) ⊢  x ∈ w → S(x) ∈ w
        apply allE' (#0 ∈' #1 →' S #0 ∈' #1) #1 _ (rfl),
        apply andE₂ _ ,
        apply hypI1 } },
    { -- x ⊢ ∀ w ( (w is inductive) → S(x) ∈ w) → S(x) ∈ ω
      apply iffE_l,
      apply allE' _ S#0,
      apply hypI,
      { simp [set.image_insert_eq] },
      { simp, } } }
end

/-- 
  Informally:  `Γ ⊢ ω is inductive`, provided `omega_ax ∈ Γ`. 
-/
def omega_inductive' {Γ} (h: omega_ax ∈ Γ) : Γ  ⊢ ω is_inductive :=
begin
  apply weak_singleton omega_ax,
  exact omega_inductive,
  exact h,
end

/--
  A formal proof that `ω` is the smallest inductive set derived from the axioms of IZF.

  Informally : `izf_ax ⊢ (ω is inductive) ∧ ∀ w ((w is inductive) → ω ⊆ w)`
-/
def omega_smallest_inductive : izf_ax ⊢ (ω is_inductive) ∧' ∀'((#0 is_inductive) →' ω ⊆' #0) :=
begin
  apply andI,
  { apply omega_inductive', simp[izf_ax], },
  { apply omega_subset_all_inductive', simp[izf_ax], },
end

end izf_proofs

/--  Main Theorem: IZF proves that ω is the smallest inductive set. -/
theorem omega_smallest_inductive_provable_within_izf : 
  ((ω is_inductive) ∧' ∀'((#0 is_inductive) →' ω ⊆' #0)) is_provable_within izf_ax :=
begin use omega_smallest_inductive end

end izf 