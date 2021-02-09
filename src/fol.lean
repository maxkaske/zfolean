import data.set
import tactic.linarith

-- use with `simp only with tls`
mk_simp_attribute tls
"Collection of definitions and lemmas for simplifying combinations of lifts and substitutions we would consider trivial."

open nat set
namespace fol
universe variable u
/--
  The language of a first-order logic consisting of functions and predicates with given arities.
-/
structure language : Type (u+1) :=
(functions : ℕ → Type u) ( predicates : ℕ → Type u)

inductive empty : ℕ → Type

def trivial_lang : language :=
{ functions := empty, predicates := empty}

variable (L : language.{u})
 
/--
  `preterm L a` is partially applied* first-order term of `L`, representing variabes as De Bruijn indices.

  * For `a=0` this is a well-formed term.
  * For `a≠0` this is a partially applied function, requiring `a` further term applications to become
    a well formed term.
-/
inductive preterm : ℕ → Type u
| var  ( index : ℕ ) : preterm 0
| func { arity : ℕ } ( f : L.functions arity ) : preterm arity
| fapp { arity : ℕ } ( t : preterm (arity+1) )  ( s : preterm 0 ) : preterm arity
export preterm

@[reducible] def term := preterm L 0
prefix `#`:max := preterm.var

variable {L}
namespace term
/--
  `lift t m i` increases the index of each `i`-free variable in `t` by `m`.

  * a variable is `i`-free if its De Bruijn index is greater than or equal to `i`.
  * Notation:  `t ↑ m ＠ i`
  * Note: We read this as "lift term `t` by `m` at `i`", which then informs the naming of later lemmas and our notation.
-/
def lift : ∀{a} , preterm L a → ℕ → ℕ → preterm L a 
| _ #x          m i := #( if i ≤ x then x+m else x)
| _ (func f)    m i := func f
| _ (fapp t s)   m i := fapp (lift t m i) (lift s m i)

end term

notation t ` ↑ `:90 m ` ＠ `:90 i:90  := term.lift t m i
notation t ` ↑₀ `:90 m :90 := term.lift t m 0

namespace term

-- unfolding lemmas for the simplifier
@[simp, tls] lemma lift_fapp {a} (t : preterm L (a+1)) (s : preterm L 0) (m i : ℕ ) 
  : (fapp t s) ↑ m ＠ i = fapp (t ↑ m ＠ i) (s ↑ m ＠ i) := by refl
@[simp, tls] lemma lift_func {a} (f : L.functions a) (m i : ℕ ) 
  : (func f) ↑ m ＠ i = func f := by refl

-- lifting of variables by cases for the simplifier
@[simp] lemma lift_var_lt {x m i : ℕ} (H : x < i) : #x ↑ m ＠ i = (#x : term L) 
  := begin unfold lift, rw if_neg (not_le.mpr H), end
@[simp, tls] lemma lift_var_eq {x m}: ((#x ↑ m ＠ x) = (#(x+m) : term L)) 
  := begin rw lift, rw if_pos x.le_refl, end
@[simp] lemma lift_var_gt {x m i} (H : i < x ) : #x ↑ m ＠ i = (#(x+m) : term L)
  := begin rw lift, rw if_pos (le_of_lt H), end
@[simp] lemma lift_var_ge {x m i} (H : i ≤ x ) : #x ↑ m ＠ i = (#(x+m) : term L)
  := begin rw lift, rw if_pos H, end
@[simp] lemma lift_var_nge {x m i : ℕ} (H : ¬ i ≤ x) : #x ↑ m ＠ i = (#x : term L) 
  := begin unfold lift, rw if_neg H, end


/--
  Lifting by `0` is trivial.
-/
@[simp, tls] lemma lift_by_0: ∀ {a} ( t : preterm L a) {i}, t ↑ 0 ＠ i = t
| _ #x         i  := by simp[lift]
| _ (func f)   _  := by refl
| _ (fapp f t) _  := begin unfold lift, congr; apply lift_by_0, end


-- A collection of various lifting lemmas
-- collected through https://github.com/coq-community/dblib/blob/master/src/DeBruijn.v
-- and www21.in.tum.de/~berghofe/papers/LFMTP06.pdf

lemma lift_lift: ∀ {a} ( t : preterm L a ) (m) {i} (n) {j} (H : j ≤ i), 
  (t ↑ m ＠ i) ↑ n ＠ j = (t ↑ n ＠ j) ↑ m ＠ (i+n) 
| _ #x          m i n j H   := 
  begin by_cases h₀ : i ≤ x,
    { have h₁ : j ≤ x := le_trans H h₀, 
      have h₂ : j ≤ x + m := le_trans h₁ (x.le_add_right m),
      simp[*, add_right_comm], },
    { have h₁ : ¬(i + n ≤  x + n) := begin intro h, exact  h₀ (le_of_add_le_add_right h) end,
      have h₂ : ¬(i + n ≤ x)      := begin intro h, exact h₁ ( le_trans h (x.le_add_right n) ) end,
      by_cases j ≤ x; simp[*], }, 
  end
| _ (func f)    _ _ _ _ _      := by refl
| _ (fapp f t)  _ _ _ _ _   := by simp*
    

lemma lift_lift_rev {a} ( t : preterm L a ) {m i} (n) {j} (H : i + m ≤ j)
    : (t ↑ m ＠ i) ↑ n ＠ j = ( t ↑ n ＠ (j-m) ) ↑  m  ＠ i :=
begin
  have h : i ≤ (j-m) := nat.le_sub_right_of_add_le H,
  have h': m ≤ j := (le_trans (m.le_add_left i) H),
  rw [lift_lift t n m h, nat.sub_add_cancel h'],
end

lemma lift_lift_merge: ∀ {a} ( t : preterm L a) {m i} (n) {j} (H : i ≤ j) (H' : j ≤ i + m), 
  (t ↑ m ＠ i ) ↑ n ＠ j = t ↑ (m+n) ＠ i
| _ #x         m i n j H H' :=  
  begin by_cases h₀ : i ≤ x,
    { have h₁ : j ≤ x + m  := le_trans H' (add_le_add_right h₀ m),
      simp[*, add_assoc], },
    { have h₁ : ¬ ( j ≤ x) := (λ h,  h₀ (le_trans H h)),
      simp[*], }, 
  end
| _ (func f)   _ _ _ _ _ _  := by refl
| _ (fapp t s) _ _ _ _ _ _  := by simp*

lemma lift_by_succ {a} ( t : preterm L a) {m i} : t ↑ (m+1) ＠ i  = ( t ↑ 1 ＠ i) ↑ m ＠ i
  := begin rw[lift_lift_merge, one_add], apply le_refl, apply le_succ, end


/-- 
  `subst t s k` subsitutes each occurences of `#k` in `t` for `s ↑ k ＠ 0` and 
  reduces the index of all variables above `k` by `1`.
-/
def subst: ∀{a}, preterm L a → term L → ℕ → preterm L a
| _ #x           s k := if x < k then #x else if k < x then #(x-1) else (s ↑ k ＠ 0)
| _ (func f)     s k := func f
| _ (fapp t₁ t₂) s k := fapp (subst t₁ s k) (subst t₂ s k)

end term

-- we use ⁄ (U+2044) instead of the usual slash / (U+002F) to avoid conflict with the divison operator
-- recommended to make a custom shortcut as the default \textfractionsolidus is quite unhandy
notation t `[`:max s ` ⁄ `:95 n `]`:0 := term.subst t s n 
#reduce #5[#2 ⁄ 1]

namespace term

-- lemmas for the simplifier
@[simp, tls] lemma subst_fapp {a} (t₁ : preterm L (a+1)) (t₂ s : preterm L 0) (k : ℕ ) : 
  (fapp t₁ t₂) [s ⁄ k] = fapp (t₁ [s ⁄ k]) (t₂ [s ⁄ k]) := by refl
@[simp, tls] lemma subst_func {a} (f : L.functions a) (s k) : 
  (func f) [s ⁄ k] = func f := by refl


@[simp] lemma subst_var_lt (s : term L) {x k : ℕ} (H : x < k) : #x[s ⁄ k] = #x := 
    begin rw subst, rw if_pos H, end
@[simp, tls] lemma subst_var_eq (s : term L) {k : ℕ}  : #k[s ⁄ k] =  s ↑ k ＠ 0 := 
    begin rw subst, repeat{ rw if_neg (lt_irrefl k) }, end
@[simp] lemma subst_var_gt (s : term L) {x k  : ℕ} (H : k < x) : #x[s ⁄ k] = #(x-1) := 
    begin rw subst, rw if_neg (lt_asymm H), rw if_pos H, end
@[simp] lemma subst_var_nle (s : term L) {x k : ℕ} (H : ¬ (x ≤ k)) : #x[s ⁄ k] = #(x-1) := 
  subst_var_gt s (not_le.mp H)

@[simp, tls] lemma subst_var0 (s : term L): #0[ s ⁄ 0 ] = s := 
    begin rw subst_var_eq, exact lift_by_0 s, end


-- substitution lemmas

lemma lift_subst : ∀ {a}  (t : preterm L a) (s: term L) (m) {i} (k) ( H: i ≤ k ),
    t [ s ⁄ k ] ↑ m ＠ i = (t ↑ m ＠ i )[ s ⁄ k+m ] 
| _ #x s m i k H := 
  begin 
    --unfold subst lift,
    apply decidable.lt_by_cases x k; intro h₁,
    { -- x < k
      have h₂ : x < k + m, from nat.lt_add_right x k m h₁, by_cases i≤x;
      simp* , },
    { -- x = k
      subst h₁, 
      simp[*, lift_lift_merge] , } ,
    { -- x > k
      have h₂ : i < x, by linarith,
      have : i ≤ x-1, from nat.le_sub_right_of_add_le (succ_le_of_lt h₂ ),
      have : i ≤ x, by linarith,
      have : 1 ≤ x, by linarith,
      simp[*, nat.sub_add_comm],
    },
  end
| _ (func f)   _ _ _ _ _ := by refl
| _ (fapp f t) _ _ _ _ _ := by simp* 

lemma subst_lift: ∀  {a}  (t : preterm L a) (s: term L) {m i k : ℕ} (H: i ≤ k) (H' : k ≤ i + m),
    (t ↑ (m+1) ＠ i) [s ⁄ k] = t ↑ m ＠ i 
| _ #x s m i k H H' := 
  begin by_cases h: i ≤ x,
    { have h₁ : k < x + (m + 1), from lt_succ_of_le (le_trans H' (add_le_add_right h m)), simp[*] , },
    { have h₁ : x < k, from lt_of_lt_of_le (lt_of_not_ge h) H, simp[*] , } 
  end
| _ (func f)   _ _ _ _ _ _ := by refl
| _ (fapp f t) _ _ _ _ _ _ := by simp* 

lemma subst_subst: ∀ {a} (t : preterm L a) (s₁) {k₁}  (s₂) {k₂} (H : k₁ ≤ k₂), 
    t[s₁ ⁄ k₁][s₂ ⁄ k₂] = t[s₂ ⁄ k₂ + 1][(s₁ [s₂ ⁄ k₂ - k₁]) ⁄ k₁] 
| _ #x s₁ k₁ s₂ k₂ H := 
  begin apply decidable.lt_by_cases x k₁; intro h₁,
    { have h₂ : x < k₂, from lt_of_lt_of_le h₁ H, 
      have h₃ : x < k₂ + 1, from lt.step h₂,
      simp[*] , },
    { subst h₁,
      have h₂ : x < k₂ + 1, from lt_succ_iff.mpr H,
      simp[*, lift_subst, nat.sub_add_cancel] , },
    { apply decidable.lt_by_cases (x-1) k₂; intro h₂,
      { have : x < k₂ + 1, from nat.lt_add_of_sub_lt_right h₂, simp[*] , },
      { have h₃: 1 ≤  x , from by linarith,
        have h₄: x  = k₂ + 1, from (nat.sub_eq_iff_eq_add h₃).mp h₂,
        subst h₄, clear h₃,
        simp[*, subst_lift, lt_irrefl] , 
      },
      { have: k₂+1 < x,   from nat.add_lt_of_lt_sub_right h₂, 
        have: k₁ < x - 1, from gt_of_gt_of_ge h₂ H,
        simp[*], }, }, 
  end
| _ (func f) _ _ _ _ _ := by refl
| _ (fapp t s) _ _ _ _ _ := by simp*

lemma subst_lift_by_lift : ∀{a} (t : preterm L a) (s : term L) (m i k : ℕ),
    (t ↑ m ＠ ( i + k + 1 ) ) [ (s ↑ m ＠ i) ⁄ k] = (t [ s ⁄ k ]) ↑ m ＠ (i+k)
| _ #x s m i k :=
  begin by_cases h₁ : i + k + 1 ≤ x,
    { -- i + k + 1 ≤ x
      have h₂ : k < x := lt_of_le_of_lt (le_add_left k i) (lt_of_succ_le h₁),
      have : k < x + m := lt_add_right k x m h₂,
      have : i + k ≤ x - 1 := nat.le_sub_right_of_add_le h₁,
      have : 1 ≤ x := one_le_of_lt h₂,
      simp [*, nat.sub_add_comm] , },
    { -- ¬ i + k + 1 ≤ x
      apply decidable.lt_by_cases x k; intro h₂,
      { -- x < k
        have : ¬ i + k ≤ x := not_le_of_lt (lt_add_left x k i h₂), simp[*] , },
      { -- x = l
        subst h₂, simp[*, lift_lift] , },
      { -- k < x
        have h₁: ¬ i+k ≤ x - 1, 
        begin
          intro h, 
          have h₃ : i + k + 1 ≤ x - 1 + 1, from succ_le_succ h,
          rw nat.sub_add_cancel (one_le_of_lt h₂) at h₃, 
          exact h₁ h₃,
        end, 
        simp[*] , }, }, 
  end
| _ (func f)     _ _ _ _ := by refl
| _ (fapp t₁ t₂) _ _ _ _ := by simp* 

lemma subst_var0_lift : ∀{a} (t : preterm L a) (m i : ℕ), (t ↑ (m+1) ＠  (i+1) )[ #0 ⁄ i] = t ↑ m ＠ (i+1)
| _ #x m i := begin apply decidable.lt_by_cases i x; intro h₀,
                { have: i+1 ≤ x, by linarith,
                have: ¬ (x + (m + 1) < i), by linarith, 
                have: i < x + (m + 1), by linarith,
                simp* , },
                { subst h₀, simp , },
                { have: ¬ (i + 1 ≤ x), by linarith, simp* , },
            end
| _ (func f) _ _ := by refl
| _ (fapp t s) _ _ := by simp* 


@[simp, tls] lemma subst_var0_lift_by_1 {a} (t : preterm L a) (i : ℕ) : (t ↑ (1) ＠  (i+1) )[#0 ⁄ i] = t := 
begin
    have h:= subst_var0_lift t 0 i,
    rw lift_by_0 at h,
    exact h,
end

@[simp, tls] lemma subst_for_0_lift_by_1: ∀ {a} (t : preterm L a) (s : term L) , (t ↑ 1 ＠ 0 )[s ⁄ 0] = t 
| _ #x _         := by refl
| _ (func f) _   := by refl
| _ (fapp t s) _ := by simp* 


/--
  Highest variable index occuring in a term (plus one).

  Examples:
  * `max_free_var #k = k+1` by definition.
  * `max_free_var t = 0` means no variables occur in `t`.
-/
def max_free_var: ∀ {a} (t : preterm L a), ℕ 
| _ #x := x+1
| _ (func f)  := 0
| _ (fapp t s) := max (max_free_var t) (max_free_var s)

lemma trivial_lift_monotone {a} {t:preterm L a} {i j: ℕ} (h: i ≤ j) (H: t ↑ 1 ＠ i = t) : t ↑ 1 ＠ j = t :=
begin
  induction j with j,
  { rwa[le_zero_iff.mp h] at H,},
  {  by_cases h': i = j+1, 
    { rwa h' at H, },
    { have h₁: i≤j, from lt_succ_iff.mp (lt_of_le_of_ne h h'),
      have h₂ := j_ih h₁,
      rw [←H, ←lift_lift t 1 1 h₁, h₂], },
  },
end

@[simp, tls] lemma lift_at_max_free_var {a} (t : preterm L a) : t ↑ 1 ＠ (max_free_var t) = t :=
begin
  induction t with T,
  { simp[max_free_var], },
  { refl },
  { unfold lift max_free_var,
    congr,
    { have t_h := le_max_left (max_free_var t_t) (max_free_var t_s),
      exact trivial_lift_monotone t_h t_ih_t, },
    { have s_h := le_max_right (max_free_var t_t) (max_free_var t_s),
      exact trivial_lift_monotone s_h t_ih_s, } }
end 

end term
variable (L)
/--
  `preformula L a` is a partially applied formula of first order predicate logic (with equality).
  This definition includes symbols for falsum `⊥'`, equality `='`, implication `→'`, 
  and `∧'`, or `∨'`, universal `∀'` and existential `∃'` quantifiers, a symbol `pred P`
  for each predicate of the language `L` and `papp φ t` for applying a term `t`.
  * For `a=0` this is a well-defined formula.
  * For `a≠0` this is a partially applied predicate, requiring `a` more term applications to become
    a well-formed formula.
-/
inductive preformula : ℕ → Type u
| bot                           : preformula 0
| eq   ( t s : term L )         : preformula 0
| imp  ( φ ψ : preformula 0 )   : preformula 0
| and  ( φ ψ : preformula 0 )   : preformula 0
| or   ( φ ψ : preformula 0 )   : preformula 0
| all  ( φ : preformula 0 )     : preformula 0
| ex   ( φ : preformula 0 )     : preformula 0 
| pred { arity : ℕ } ( P : L.predicates arity )                  : preformula arity 
| papp { arity : ℕ } ( φ : preformula (arity+1) ) ( t : term L ) : preformula arity

@[reducible] def formula := preformula L 0

variable {L}

notation `⊥'` := preformula.bot 

infix ` =' `:100 := preformula.eq  

prefix `∀'`:110 := preformula.all
prefix `∃'`:110 := preformula.ex 

infixr ` →' `:80 := preformula.imp
infixr ` ∨' `:85 := preformula.or
infixr ` ∧' `:90 := preformula.and 

@[simp] def iff (f₁ f₂ : formula L) : formula L := ( f₁ →' f₂ ) ∧'  ( f₂ →' f₁ )
infix ` ↔' `:70 := iff -- input \<=>

@[simp] def not (f: formula L) : formula L := (f →' ⊥') 
prefix `¬'`:115 := not

def top : formula L  := ¬' ⊥'
notation `⊤'` := top

#check ¬' (#0 =' #1)
export preformula

/- On De Bruijn indices:
  

-/

namespace formula

/--
  `lift φ m i` increases the index of each _free_ variable greater or equal to `i` in `φ` by `m`.
  Intuitively, this adds a batch of `m` new free variables
  * Notation:  `φ ↑ m ＠ i`
  * Note: We read this as "lift term `t` by `m` at `i`", which then informs the naming of later lemmas and our notation.
-/

@[simp, reducible] def lift : ∀{a} , preformula L a → ℕ → ℕ → preformula L a 
| _ ⊥'  _ _         := ⊥'  
| _ (t =' s) m i    := (term.lift t m i) =' (term.lift s m i)
| _ ( φ →' ψ ) m i  := (lift φ m i) →' (lift ψ  m i)
| _ ( φ ∧' ψ ) m i  := (lift φ m i) ∧' (lift ψ  m i)
| _ ( φ ∨' ψ ) m i  := (lift φ m i) ∨' (lift ψ  m i)
| _ ( ∀' φ ) m i    := ∀' (lift φ m (i+1))
| _ ( ∃' φ ) m i    := ∃' (lift φ m (i+1))
| _ (pred P) _ _    := pred P
| _ (papp φ t) m i  := papp (lift φ m i) (term.lift t m i)
end formula


notation f ` ↑ `:90 m ` ＠ `:90 i :90 := formula.lift f m i
notation f ` ↑₀ `:max n  := formula.lift f n 0

#reduce #3 ↑ 3 ＠ 1
#reduce (#3 =' #0) ↑ 3 ＠ 1

namespace formula
open preformula


lemma all_lift {φ : formula L} {m i} : ∀'( φ ↑ m ＠ (i+1) ) = (∀' φ) ↑ m ＠ i := by refl


@[simp, tls] lemma lift_by_0: ∀ {a} ( φ : preformula L a) {i}, φ ↑ 0 ＠ i = φ
| _ ⊥' _            := by refl
| _ (t =' s) _      := by simp
| _ ( φ →' ψ ) _    := begin rw lift, congr; exact lift_by_0 _, end
| _ ( φ ∧' ψ ) _    := begin rw lift, congr; exact lift_by_0 _, end
| _ ( φ ∨' ψ ) _    := begin rw lift, congr; exact lift_by_0 _, end
| _ ( ∀' φ ) _      := begin rw lift, congr, exact lift_by_0 φ, end
| _ ( ∃' φ ) _      := begin rw lift, congr, exact lift_by_0 φ, end
| _ ( pred P ) _    := by refl
| _ ( papp φ t ) _  := begin rw lift, congr, exact lift_by_0 φ, exact term.lift_by_0 t, end


lemma lift_lift: ∀{a} ( φ : preformula L a) (m) {i} (n) {j} ( H : j ≤ i ),
    ( φ ↑ m ＠ i ) ↑ n ＠ j = ( φ ↑ n ＠ j) ↑ m ＠ (i+n)     -- lift(lift φ m i) n j = lift (lift φ  n j) m (i+n)
| _ ⊥' _ _ _ _ _             := by refl
| _ ( t =' s ) _ _ _ _ _     := by simp[*, term.lift_lift]
| _ ( φ →' ψ ) _ _ _ _ _     := by simp[*]
| _ ( φ ∧' ψ ) _ _ _ _ _     := by simp[*]
| _ ( φ ∨' ψ ) _ _ _ _ _     := by simp[*]
| _ ( ∀' φ ) _ _ _ _ _       := by simp[*, add_right_comm]
| _ ( ∃' φ ) _ _ _ _ _       := by simp[*, add_right_comm]
| _ ( pred P ) _ _ _ _ _     := by refl
| _ ( papp φ t ) _ _ _ _ _   := by simp[*, term.lift_lift]

lemma lift_lift_reverse {a} ( φ : preformula L a) {m i} (n) {j} (H : i + m ≤ j) :
    ( φ ↑ m ＠ i ) ↑ n ＠ j = ( φ  ↑ n ＠  (j-m) ) ↑ m ＠ i := -- lift (lift f m i) n j = lift (lift f n (j-m)) m i
begin
    have h : i ≤ (j-m), from nat.le_sub_right_of_add_le H,
    have h': m ≤ j, from (le_trans (m.le_add_left i) H),
    rw [lift_lift φ n m h, nat.sub_add_cancel h'],
end

lemma lift_lift_merge: ∀ {a} ( φ : preformula L a ) {m i} (n) {j} (H : i ≤ j) (H' : j ≤ i + m),
    ( φ ↑ m ＠ i ) ↑ n ＠ j = φ ↑ (m+n) ＠ i
| _ ⊥' _ _ _ _ _ _           := by refl 
| _ ( t =' s) _ _ _ _ _ _    := by simp[*, term.lift_lift_merge]
| _ ( φ →' ψ ) _ _ _ _ _ _   := by simp[*]
| _ ( φ ∧' ψ ) _ _ _ _ _ _   := by simp[*]
| _ ( φ ∨' ψ ) _ _ _ _ _ _   := by simp[*]
| _ ( ∀' φ ) _ _ _ _ _ _     := by simp[*, add_right_comm]
| _ ( ∃' φ ) _ _ _ _ _ _     := by simp[*, add_right_comm]
| _ ( pred P ) _ _ _ _ _ _   := by refl
| _ ( papp φ t ) _ _ _ _ _ _ := by simp[*, term.lift_lift_merge]

@[simp, tls] lemma lift_at_lift_merge {a} ( φ : preformula L a ) (m i n):
    ( φ ↑ m ＠ i ) ↑ n ＠ i = φ ↑ (m+n) ＠ i := lift_lift_merge φ n (le_rfl) (i.le_add_right m)



lemma lambda_lift_lift {a} (m) {i} (n) {j} (H : j≤i) : 
    (λ ( φ :preformula L a),  ( φ ↑ m ＠ i ) ↑ n ＠ j ) = (λ φ, ( φ ↑ n ＠ j) ↑ m ＠ (i+n)) :=
begin funext, apply lift_lift, exact H, end


@[simp, tls] def subst :  ∀{a} , preformula L a → term L → ℕ → preformula L a
| _ ⊥'  _ _         := ⊥'  
| _ ( t₁ =' t₂) s k := (term.subst t₁ s k) =' (term.subst t₂ s k)
| _ ( φ →' ψ ) s k  := (subst φ s k) →' (subst ψ  s k)
| _ ( φ ∧' ψ ) s k  := (subst φ s k) ∧' (subst ψ  s k)
| _ ( φ ∨' ψ ) s k  := (subst φ s k) ∨' (subst ψ  s k)
| _ ( ∀' φ ) s k    := ∀' (subst φ  s (k+1))
| _ ( ∃' φ ) s k    := ∃' (subst φ  s (k+1))
| _ (pred P) _ _    := pred P
| _ (papp φ t) s k  := papp (subst φ s k) (term.subst t s k)

end formula

notation φ `[`:max t ` ⁄ `:95 n `]`:0 := formula.subst φ t n

#reduce #5[#2 ⁄ 1]
#reduce (#5 =' #4)[#0 ⁄ 5] 
 
namespace formula
open preformula

-- lift and substitution lemmas for formulas; follow directly from the corresponding lemmas for terms

lemma lift_subst: ∀ {a}  ( φ : preformula L a) (s: term L) ( m i k : ℕ ) (h': i ≤ k),
     φ[s ⁄ k]↑ m ＠ i = (φ ↑ m ＠  i)[s ⁄ (k+m)]  -- lift (subst f s k) m i = subst ( lift f m i) s (k+m)
| _ ⊥' _ _ _ _ _            := by refl
| _ (t₁ =' t₂) _ _ _ _ _    := by simp[*, term.lift_subst]
| _ ( φ →' ψ ) _ _ _ _ _    := by simp[*]
| _ ( φ ∧' ψ ) _ _ _ _ _    := by simp[*]
| _ ( φ ∨' ψ ) _ _ _ _ _    := by simp[*]
| _ ( ∀' φ ) _ _ _ _ _      := by simp[*, add_right_comm]
| _ ( ∃' φ ) _ _ _ _ _      := by simp[*, add_right_comm]
| _ ( pred P ) _ _ _ _ _    := by refl
| _ ( papp φ t ) _ _ _ _ _  := by simp[*, term.lift_subst]

lemma subst_lift : ∀ {a}  ( φ : preformula L a) (s: term L) {m i k : ℕ } (H: i ≤ k) (H' : k ≤ i + m),
    ( φ ↑ (m+1) ＠ i )[ s ⁄ k ] = φ ↑ m ＠ i -- subst ( lift f (m+1) i) s k = lift f m i
| _ ⊥' _ _ _ _ _ _          := by refl
| _ (t₁ =' t₂) _ _ _ _ _ _  := by simp[*, term.subst_lift]
| _ ( φ →' ψ ) _ _ _ _ _ _  := by simp[*]
| _ ( φ ∧' ψ ) _ _ _ _ _ _  := by simp[*]
| _ ( φ ∨' ψ ) _ _ _ _ _ _  := by simp[*]
| _ ( ∀' φ ) _ _ _ _ _ _    := by simp[*, add_right_comm]
| _ ( ∃' φ ) _ _ _ _ _ _    := by simp[*, add_right_comm]
| _ (pred P) _ _ _ _ _ _    := by refl
| _ ( papp φ t) _ _ _ _ _ _ := by simp[*, term.subst_lift]

lemma subst_subst : ∀ {a} ( φ : preformula L a) (s₁) {k₁} (s₂) {k₂} ( H : k₁ ≤ k₂ ), 
    φ [ s₁ ⁄ k₁] [ s₂ ⁄ k₂] = φ [ s₂ ⁄ k₂ + 1] [ (s₁ [s₂ ⁄ k₂ - k₁] ) ⁄ k₁ ] 
    -- subst ( subst f s₁ i) s₂ j = subst (subst f s₂ (j+1)) (subst s₁ s₂ (j-i) ) i
| _ ⊥' _ _ _ _ _            := by refl
| _ (t₁ =' t₂) _ _ _ _ _    := by simp[*, term.subst_subst]
| _ ( φ →' ψ ) _ _ _ _ _    := by simp[*]
| _ ( φ ∧' ψ ) _ _ _ _ _    := by simp[*]
| _ ( φ ∨' ψ ) _ _ _ _ _    := by simp[*]
| _ ( ∀' φ ) _ _ _ _ _      := by simp[*, add_right_comm]
| _ ( ∃' φ ) _ _ _ _ _      := by simp[*, add_right_comm]
| _ (pred P) _ _ _ _ _      := by refl
| _ (papp φ t) _ _ _ _ _    := by simp[*, term.subst_subst]


lemma subst_lift_in_lift : ∀{a} ( φ : preformula L a) (s : term L) (m i k),
    (φ ↑ m ＠ (i + k + 1)) [ (s ↑ m ＠ i) ⁄ k] = φ[s ⁄ k] ↑ m ＠ (i+k) --subst (lift f m (i + k + 1)) (lift s m i) k = lift (subst f s k) m (i + k)
| _ ⊥' _ _ _ _          := by refl
| _ (t₁ =' t₂) _ _ _ _  := by simp[*, term.subst_lift_by_lift]
| _ ( φ →' ψ ) _ _ _ _  := by simp[*]
| _ ( φ ∧' ψ ) _ _ _ _  := by simp[*]
| _ ( φ ∨' ψ ) _ _ _ _  := by simp[*]
| _ (∀' φ ) s m i k     := begin have := subst_lift_in_lift φ s m i (k+1), rw[add_succ i k] at this, simp[*, add_right_comm], end
| _ (∃' φ ) s m i k     := begin have := subst_lift_in_lift φ s m i (k+1), rw[add_succ i k] at this, simp[*, add_right_comm], end
| _ (pred P) _ _ _ _    := by refl
| _ (papp φ t) _ _ _ _  := by simp[*, term.subst_lift_by_lift]

-- lemma subst0_subst_formula {a} (φ : preformula L a) (s₁ s₂ : term L) (k₂):
--     φ [ s₁ ⁄ 0] [ s₂ ⁄ k₂] = φ [ s₂ ⁄ k₂ + 1] [ (s₁ [s₂ ⁄ k₂ ] ) ⁄ 0 ] := subst_subst φ s₁ s₂ (k₂.zero_le)

@[tls] lemma subst0_lift_by_lift {a}  (φ : preformula L a) {s : term L} {m i:ℕ } :
    (φ ↑ m ＠ (i + 1) ) [ (s ↑ m ＠ i) ⁄ 0] = φ[s ⁄ 0] ↑ m ＠ i := subst_lift_in_lift φ s m i 0


@[tls] lemma subst_at_lift {a} (φ  : preformula L a) (m) (s : term L) (k)  : ( φ ↑ (m+1) ＠  k)[s ⁄ k] =  φ ↑ m ＠ k
    := subst_lift φ s (le_refl k) (le.intro rfl)

@[tls] lemma subst_var0_lift : ∀{a} (φ : preformula L a) (m i : ℕ), (φ ↑ (m+1) ＠  (i+1) )[ #0 ⁄ i] = φ ↑ m ＠ (i+1)
| _ ⊥'  _ _         := by refl 
| _ ( t₁ =' t₂) m i := by simp[term.subst_var0_lift]
| _ ( φ →' ψ ) m i  := by simp*
| _ ( φ ∧' ψ ) m i  := by simp*
| _ ( φ ∨' ψ ) m i  := by simp*
| _ ( ∀' φ ) m i    := by simp*
| _ ( ∃' φ ) m i    := by simp*
| _ (pred P) _ _    := by refl
| _ (papp φ t) m i  := by simp[*, term.subst_var0_lift]

@[tls] lemma subst_var0_lift_by_1 {a}  (φ : preformula L a)  (i : ℕ) : (φ ↑ 1 ＠  (i+1) )[#0 ⁄ i] = φ := 
begin
  have h:= subst_var0_lift φ 0 i,
  rwa lift_by_0 at h,
end

lemma subst_var0_for_0_lift_by_1{a}  (φ : preformula L a) : (φ ↑ 1 ＠ 1 )[#0 ⁄ 0] = φ := subst_var0_lift_by_1 φ 0



@[simp, tls] lemma subst_for_0_lift_by_1: ∀ {a} ( φ : preformula L a) (s : term L), (φ ↑ 1 ＠ 0 )[s ⁄ 0] = φ 
| _ ⊥' _          := by refl
| _ (t₁ =' t₂) _  := by simp[*, term.subst_for_0_lift_by_1]
| _ ( φ →' ψ ) _  := by simp[*]
| _ ( φ ∧' ψ ) _  := by simp[*]
| _ ( φ ∨' ψ ) _  := by simp[*]
| _ ( ∀'φ ) s     := begin dsimp, congr, have h:= subst_at_lift φ 0 s (0+1), rw lift_by_0 at h, exact h, end
| _ ( ∃'φ ) s     := begin dsimp, congr, have h:= subst_at_lift φ 0 s (0+1), rw lift_by_0 at h, exact h, end
| _ (pred P) _    := by refl
| _ (papp φ t) _  := by simp[*, term.subst_lift_by_lift]

-- a  i-closed formula is j-closed for j≥i
lemma trivial_lift_monotone {a} {φ : preformula L a} {i j} 
  (H : φ ↑ 1 ＠ i = φ) (h : i ≤ j) : φ ↑ 1 ＠ j = φ :=
begin
  induction j with j,
  { rwa[le_zero_iff.mp h] at H, },
  { by_cases h': i = j+1, 
    { rwa h' at H, },  
    { have h₁: i≤j, from lt_succ_iff.mp (lt_of_le_of_ne h h'),
      have h₂ := j_ih h₁,
      rw [←H, ←lift_lift φ 1 1 h₁, h₂], }, },
end 

/--
  `alls k φ` is the formula obtained by binding the the first `k` free variables in `φ` with universal quantifiers.
-/
def alls : ∀ (k:ℕ) (φ: formula L) , formula L
| 0     φ   := φ 
| (k+1) φ   := ∀' (alls k φ )

lemma all_alls: ∀ (φ: formula L) (k:ℕ) , ∀' (alls k φ) = alls k (∀'φ) 
| φ 0 := by refl
| φ (k+1) := begin unfold alls, congr' 1, apply all_alls, end

lemma alls_succ (k) (φ : formula L) : alls (k+1) φ = alls k (∀' φ) := begin rw [alls, all_alls], end


lemma alls_alls: ∀ (φ: formula L) (m n:ℕ) , alls n (alls m φ) = alls m (alls n φ)
| φ 0 n := by refl
| φ (m+1) n := begin rw alls, rw ←all_alls _ _, rw alls_alls _ m n, refl, end

lemma alls_lift : ∀  (φ: formula L) (m i n:ℕ), alls n (φ ↑ m ＠ (i+n)) = (alls n φ) ↑ m ＠ i
| φ m i 0 := by refl
| φ m i (n+1) := begin dsimp[alls], congr, rw ←succ_add_eq_succ_add i n, apply alls_lift,end

lemma alls_at_lift  (φ: formula L) (m n:ℕ) : alls n (φ ↑ m ＠ n) = (alls n φ) ↑ m ＠ 0 :=
begin 
  let h := alls_lift φ m 0 n, 
  rwa zero_add at h, 
end

/--
  `substs k i j φ` is the formula `φ[#(k+i) ⁄ k+j]...[#(1+i) ⁄ 1+j][#i ⁄ j]`.
-/
def substs : ∀(k i j: ℕ ) ( φ: formula L), formula L
| 0 i j φ  := φ 
| (k+1) i j φ := substs k i j (φ [#(k+i) ⁄ (k+j)])

lemma substs_succ (k i j: ℕ ) (φ : formula L): substs (k+1) i j φ = (substs k (i+1) (j+1) φ) [ #i ⁄ j] :=
begin
  induction k generalizing φ,
  { simp[substs] },
  { simp[*,substs, succ_add_eq_succ_add] }
end 

lemma all_substs {k i j}{φ : formula L} : ∀'(substs k i (j+1) φ) = substs k i j ∀'φ :=
begin
    induction k generalizing φ,
    { dsimp[substs], refl },
    { simp[*,substs, succ_add_eq_succ_add, add_assoc] }
end


-- we need to be able to talk about formulas φ( x_1 , ... , x_n) with free variables among x_1, ... , x_n
-- wlog #n is the "outermost" (i.e. the highest) free variable in our De Bruijn representation of φ
-- then lifting φ at n+1 does not change the formula
-- thus we obtain the following definition
/--
  A formula `φ` is `k`-closed if lifting `φ ↑ 1 ＠ k` is the identity. 

  Intuitively this means that `φ` has free variables among `x₁ ... xₖ`.
-/
@[simp, reducible] def closed {a} (k : ℕ) ( φ : preformula L a) := φ ↑ 1 ＠ k = φ 

/--
  A sentence is a `0`-closed formula, i.e. a formula without free variables.
-/
@[simp, reducible] def sentence (φ  : formula L) := closed 0 φ 
postfix ` is_sentence'`:max := sentence

-- quantification of closed formulas
lemma closed_all {φ : formula L} {k} (H : closed (k+1) φ) : closed k (∀' φ) :=
begin
  dsimp, congr, exact H,
end

lemma closed_ex  {φ : formula L} {k} (H : closed (k+1) φ) : closed k (∃' φ) :=
begin
  dsimp, congr, exact H,
end

-- lifting a k-closed formula at l ≥ k is trivial
lemma lift_closed_id_h { φ : formula L} {k} (H : closed k φ) (m i) : φ ↑ m ＠ (k+i) = φ :=
begin
  induction m generalizing φ,
  { apply lift_by_0, },
  { rw [succ_eq_add_one, ←lift_lift_merge φ 1 (le_refl _ ) (le.intro rfl), m_ih H],
    apply trivial_lift_monotone H (le.intro rfl) ,
  },
end

lemma lift_closed_id { φ : formula L} {k} (H : closed k φ) (m) {l} (h : k ≤ l): (φ ↑ m ＠ l) = φ :=
begin
    cases le_iff_exists_add.mp h with i h_i,
    subst h_i, exact lift_closed_id_h H m i,
end

-- lifting (a set of) sentences is always trivial
lemma lift_sentence_id {x: formula L} (H: sentence x) { m i } :  (x ↑ m ＠ i) = x 
  := lift_closed_id H m (i.zero_le)

lemma lift_set_of_sentences_id {Γ : set $ formula L} (H : ∀ ϕ ∈ Γ, sentence ϕ) {m i} 
  : (λ ϕ: formula L, ϕ ↑ m ＠ i) '' Γ = Γ :=
begin
  apply ext, intro x,
  apply iff.intro,
  { intro h_x, rw mem_image_eq at h_x, 
    cases h_x with y h', 
    have yx:= h'.right, 
    have y_h := h'.left, 
    subst yx, rwa lift_sentence_id (H y y_h), }, 
  { intro h, rw mem_image_eq, use x, exact ⟨h, lift_sentence_id (H x h)⟩, },
end

-- substituting in a k-closed formula the l-th free variable with l ≥ k is trivial
lemma subst_closed_id_h { φ : formula L} (t:term L)  {k} (i) ( H : closed k φ) : (φ [t ⁄ k+i]) = φ :=
begin
  have h := subst_at_lift φ 0 t (k+i),
  repeat {rwa lift_closed_id_h H _ _ at h,},
end

lemma subst_closed_id {φ : formula L}{i}  (H : closed i φ)  (t:term L) {k} (h : i≤k) : (φ [t ⁄ k]) = φ :=
begin
  cases le_iff_exists_add.mp h with j h_j,
  subst h_j, exact subst_closed_id_h t j H,
end

-- substituting in (a set of) sentences is always trivial
lemma subst_sentence_id { φ : formula L} ( H : sentence φ )  {t: term L} {k:ℕ} :  (φ [t ⁄ k]) = φ 
  := subst_closed_id H t (k.zero_le)

lemma subst_set_of_sentences_id {Γ : set $ formula L} {t k} (H : ∀f ∈ Γ, sentence f)
  : (λ (ϕ: formula L), ϕ[t ⁄ k]) '' Γ = Γ :=
begin
  apply ext, intro x,
  apply iff.intro,
  { intro h_x, rw mem_image_eq at h_x, 
    cases h_x with y h', 
    have yx := h'.right, 
    have h_y := h'.left, 
    subst yx, rwa subst_sentence_id (H y h_y), }, 
  { intro h, rw mem_image_eq, use x, exact ⟨h, subst_sentence_id (H x h)⟩, },
end

/--
  Intuitively, `max_free_var φ = 0` means that `φ` has no free variables,
  while  `max_free_var φ = k+1` means that `xₖ` is a free variable of `φ`.
-/
def max_free_var :  ∀ {a} (φ: preformula L a), ℕ 
| _ ⊥'           := 0
| _ (t₁ =' t₂)   := max (term.max_free_var t₁) ( term.max_free_var t₂)
| _ ( ∀'φ )      := (max_free_var φ) - 1
| _ ( ∃'φ )      := (max_free_var φ) - 1
| _ ( φ →' ψ )   := max (max_free_var φ) ( max_free_var ψ )
| _ ( φ ∧' ψ )   := max (max_free_var φ) ( max_free_var ψ )
| _ ( φ ∨' ψ )   := max (max_free_var φ) ( max_free_var ψ )
| _ (pred P)     := 0
| _ (papp φ t)   := max (max_free_var φ) ( term.max_free_var t )

-- The above intuition tells us that every formula should be closed at its maximal free variable 
lemma closed_max_free_var {a} (φ : preformula L a) : closed (max_free_var φ) φ :=
begin
  unfold closed,
  induction φ,
  { refl },
  { have h₁ := term.trivial_lift_monotone (le_max_left (term.max_free_var φ_t)  (term.max_free_var φ_s)) (term.lift_at_max_free_var φ_t),
    have h₂ := term.trivial_lift_monotone (le_max_right (term.max_free_var φ_t) (term.max_free_var φ_s)) (term.lift_at_max_free_var φ_s),
    rw[max_free_var, formula.lift, h₁,h₂] },
  { have h₁:= trivial_lift_monotone φ_ih_φ (le_max_left  (max_free_var φ_φ) (max_free_var φ_ψ)),
    have h₂:= trivial_lift_monotone φ_ih_ψ (le_max_right (max_free_var φ_φ) (max_free_var φ_ψ)),
    rw[max_free_var, formula.lift, h₁,h₂] },
  { have h₁:= trivial_lift_monotone φ_ih_φ (le_max_left  (max_free_var φ_φ) (max_free_var φ_ψ)),
    have h₂:= trivial_lift_monotone φ_ih_ψ (le_max_right (max_free_var φ_φ) (max_free_var φ_ψ)),
    rw[max_free_var, formula.lift, h₁,h₂] },
  { have h₁:= trivial_lift_monotone φ_ih_φ (le_max_left  (max_free_var φ_φ) (max_free_var φ_ψ)),
    have h₂:= trivial_lift_monotone φ_ih_ψ (le_max_right (max_free_var φ_φ) (max_free_var φ_ψ)),
    rw[max_free_var, formula.lift, h₁,h₂] },
  { have h := trivial_lift_monotone φ_ih (nat.le_sub_add (max_free_var φ_φ) 1),
    rw[formula.lift, max_free_var, h], },
  { have h := trivial_lift_monotone φ_ih (nat.le_sub_add (max_free_var φ_φ) 1),
    rw[formula.lift, max_free_var, h] },
  { refl },
  { have h₁:= trivial_lift_monotone φ_ih (le_max_left (max_free_var φ_φ) (term.max_free_var φ_t)),
    have h₂:= term.trivial_lift_monotone (le_max_right (max_free_var φ_φ) (term.max_free_var φ_t)) (term.lift_at_max_free_var φ_t) ,
    rw[max_free_var, formula.lift, h₁, h₂] }
end 

/--
  The (universal) closure of a `k`-closed formula.
  Intuitively, given a formula `φ` with free variables among `x₁ ... xₖ` 
  the closure is `∀xₖ ... ∀x₁ φ`. 
-/
@[reducible] def closure (φ: formula L) {k} (H: closed k φ) := alls k φ

lemma closure_is_sentence  { φ : formula L} {k} (H : closed k φ) : (closure φ H) is_sentence' :=
begin
  induction k generalizing φ,
  { exact H, },
  { unfold closure,
    rw[alls, all_alls],
    exact k_ih (closed_all H), },
end

lemma lambda_lift_subst_formula {a} {s: term L} { m i k : ℕ } (h': i ≤ k) 
  : (λ (ϕ: preformula L a), lift (subst ϕ s k) m i) = (λ ϕ, subst ( lift ϕ m i) s (k+m)) :=
begin funext, apply lift_subst, assumption, end

end formula
export formula

local notation φ :: Γ := insert φ Γ 

/--
  An implementation of a Natural Deduction proof system for intuitionistic first-order predicate logic
  with equality.
-/

inductive proof : (set $ formula L) → formula L → Type u
| hypI {Γ} {φ} (h : φ ∈ Γ) : proof Γ φ 
| botE {Γ} {φ} (H : proof Γ  ⊥' ) : proof Γ φ
-- implication
| impI  {Γ} {φ ψ}   (H : proof (φ::Γ) ψ) : proof Γ (φ →' ψ)
| impE  {Γ} (φ) {ψ} (H₁ : proof Γ φ) (H₂ : proof Γ (φ →' ψ)) : proof Γ ψ
-- conjunction
| andI  {Γ} {φ ψ} (H₁ : proof Γ φ) 
                  (H₂ : proof Γ ψ) : proof Γ (φ ∧' ψ) 
| andE₁ {Γ} {φ} (ψ) (H : proof Γ (φ ∧' ψ)) : proof Γ φ
| andE₂ {Γ} (φ) {ψ} (H : proof Γ (φ ∧' ψ)) : proof Γ ψ
-- disjunction
| orI₁ {Γ} {φ ψ} (H : proof Γ φ) : proof Γ (φ ∨' ψ)
| orI₂ {Γ} {φ ψ} (H : proof Γ ψ) : proof Γ (φ ∨' ψ)
| orE  {Γ}  (φ ψ) {χ} (H  : proof Γ (φ ∨' ψ)) 
                      (H₁ : proof (φ::Γ) χ) 
                      (H₂ : proof (ψ::Γ) χ) : proof Γ χ
-- quanitfication
| allI  {Γ} {φ} (H : proof ( (λ (ϕ:formula L) , ϕ ↑₀ 1) '' Γ ) φ) : proof Γ (∀'φ)
| allE  {Γ} (φ) {t} (H : proof Γ (∀'φ)) : proof Γ (φ [t ⁄ 0])
| exI   {Γ φ} (t) (H : proof Γ (φ[t ⁄ 0])) : proof Γ  (∃'φ)
| exE   {Γ ψ} (φ) (H₁ : proof Γ (∃'φ) ) 
                  (H₂ : proof ( φ :: ((λ (ϕ: formula L) , ϕ ↑₀ 1) '' Γ) ) (ψ ↑₀ 1)) : proof Γ ψ
-- equality
| eqI {Γ} (t) : proof Γ (t =' t)
| eqE {Γ} {s t φ } (H₁ : proof Γ (s =' t)) (H₂ : proof Γ (φ[s ⁄ 0])) : proof Γ (φ [t ⁄ 0])
infix ` ⊢ `:55 := proof 

/-- 
  `provable Γ φ` says that there exists a proof of `φ` under the hypotheses in `Γ`,
  i.e. it is a fancy way to say that the type `Γ ⊢ φ` is non-empty. 
-/
def provable (φ : formula L) (Γ)  : Prop := nonempty (Γ ⊢ φ)
infix ` is_provable_within `:100 := provable

/--
  The law of excluded middle for when we want to argue in classical logic.
-/
def lem : set $ formula L := { (φ ∨' ¬'φ) |  (φ: formula L) (h: φ is_sentence') } -- do we need the extra condition?
namespace proof
/--
  Rule for weakening the context of a proof by allowing more premises.
-/
def weak {Δ φ}  (Γ: set $ formula L ) ( H : Γ ⊢ φ ) (h: Γ ⊆ Δ): (Δ ⊢ φ) :=
begin
    induction H generalizing Δ,
    { apply hypI (h H_h) },
    { apply botE, apply H_ih, assumption },

    { apply impI, apply H_ih, apply insert_subset_insert, assumption },
    { apply impE, apply H_ih_H₁, assumption, 
      apply H_ih_H₂, assumption },

    { apply andI,  apply H_ih_H₁, exact h, 
      apply H_ih_H₂, exact h},
    { apply andE₁, apply H_ih, exact h },
    { apply andE₂, apply H_ih, exact h },

    { apply orI₁, apply H_ih, exact h, },
    { apply orI₂, apply H_ih, exact h, },
    { apply orE,  apply H_ih_H, exact h, 
      apply H_ih_H₁, apply insert_subset_insert, exact h, 
      apply H_ih_H₂, apply insert_subset_insert, exact h},

    { apply allI, apply H_ih, exact image_subset _ h,},
    { apply allE, apply H_ih, exact h},

    { apply exI, apply H_ih, exact h},
    { apply exE, apply H_ih_H₁, exact h, 
      apply H_ih_H₂, apply insert_subset_insert, exact image_subset _ h,},

    { apply eqI, },
    { apply eqE, apply H_ih_H₁ h, apply H_ih_H₂ h, },
end

/--
  Proof rule for weakening the context of a proof by inserting a single premise.
-/
def weak1 {Γ} {φ ψ: formula L} ( H: Γ ⊢ ψ ) :  (φ::Γ) ⊢ ψ := weak Γ H (subset_insert φ Γ)

/--
  Proof rule for weakening the context of a proof from a single premise.
-/
def weak_singleton {Γ} (φ) {ψ: formula L} ( H: { φ } ⊢ ψ ) (h: φ ∈ Γ ) :  Γ ⊢ ψ :=
begin
  apply weak {φ} H,
  assume x xh,
  rw mem_singleton_iff at xh,
  subst xh,
  assumption,
end

-- QoL rules for hypothesis
def hypI1 {Γ} (φ: formula L)  : (φ :: Γ ) ⊢ φ := hypI (mem_insert φ Γ)

def hypI2 {Γ} (φ ψ: formula L)  : (φ :: ψ :: Γ ) ⊢ ψ := 
begin
  apply hypI, right, exact mem_insert ψ Γ,
end
/--
  Rule for top introduction.
-/
def topI {Γ: set $ formula L} : Γ ⊢ ⊤' := begin apply impI, apply hypI1, end


-- rules for implications
def impE_insert {Γ} {φ ψ: formula L} (H₁ : Γ ⊢ (φ →' ψ )) : φ :: Γ ⊢ ψ  :=
begin
  apply impE φ, 
  apply hypI1, 
  apply weak1,
  assumption,
end

/--
  Proof rule for reflexivity of implications.
-/
def impI_refl {Γ} (φ : formula L) : Γ ⊢ (φ →' φ) := 
begin
    apply impI, apply hypI1,
end

/--
  Proof rule for transivity of implications.
-/
def impI_trans  {Γ} (φ ψ χ : formula L) (H₁: Γ ⊢ (φ →' ψ )) (H₂ : Γ ⊢ (ψ  →' χ )) : Γ ⊢ (φ  →' χ) :=
begin
  apply impI, 
  apply impE ψ, 
  apply impE_insert H₁,
  apply weak1 H₂,
end

/--
  QoL proof rule for universal quantification elimination.
-/
def allE' {Γ} (φ) (t: term L) {ψ}  (H : Γ ⊢ (∀'φ)) (h: ψ  = φ[t ⁄ 0]) : Γ ⊢ ψ :=
begin subst h, apply allE, assumption, end

/--
  Proof rule for a common case of universal quantification elimination.
-/
def allE_var0 {Γ} {φ: formula L}  (H : Γ ⊢ (∀'φ) ↑ 1 ＠ 0) : Γ ⊢ φ  :=
begin
    apply allE' (φ ↑ 1 ＠  1) #0,
    { exact H, }, 
    { symmetry, exact subst_var0_lift_by_1 φ 0, } 
end


/--
  Proof rule for equality elimination. _(QoL)_
-/
def eqE' {Γ} {ψ}  (s t) (φ : formula L) (H₁ : Γ ⊢ (s =' t)) (H₂ : Γ ⊢ (φ [s ⁄ 0])) (h:  ψ = φ[t ⁄ 0]) : Γ ⊢ ψ :=
begin rw h, apply eqE H₁ H₂, end

/--
  Proof rule for congruence introduction.
-/
def congrI {Γ} {t s₁ s₂: term L} (H :  Γ ⊢ (s₁ =' s₂)) :  Γ ⊢ ( t[s₁ ⁄ 0] =' t[s₂ ⁄ 0] ):=
begin
  apply eqE' s₁ s₂ (( (t[s₁⁄ 0] ↑ 1 ＠ 0 )=' t)) H;
  rw [subst, term.subst_for_0_lift_by_1 (term.subst t _ 0) _],
  apply eqI,
end
/--
  Proof rule for congruence introduction. _(QoL)_
-/
def congrI' {Γ} {t₁ s₁ t₂ s₂ : term L} (t) (H: Γ ⊢ s₁ =' s₂) 
  (h₁: t₁ = t[s₁ ⁄ 0]) (h₂: t₂ = t[s₂ ⁄ 0]) : Γ ⊢ (t₁ =' t₂) := 
begin rw [h₁, h₂], apply congrI H, end


/--
  Proof rule for reflexivity of equality.
-/
def eqI_refl {Γ} (t: term L): Γ ⊢ (t =' t) := @eqI L Γ t
/--
  Proof rule for symmetry of equality.
-/
def eqI_symm {Γ} (s t : term L) (H : Γ ⊢ (s =' t)) : Γ ⊢ (t =' s) :=
begin
    apply eqE' s t (#0 =' (s ↑ 1 ＠ 0)) H;
    rw [subst, term.subst_var0, term.subst_for_0_lift_by_1],
    apply eqI, 
end
/--
  Proof rule for transitivity of equality.
-/
def eqI_trans {Γ} ( s t u : term L) (H₁ : Γ ⊢ (s =' t) ) (H₂ : Γ ⊢ (t =' u)) : proof Γ ( s =' u) :=
begin
  apply eqE' t u ((s ↑ 1 ＠ 0) =' #0) H₂;
  rw[subst, term.subst_for_0_lift_by_1, term.subst_var0], 
  assumption,
end


/--
  Proof rule for introducing a biconditional.
-/
def iffI {Γ} {φ ψ : formula L} (H₁ : Γ ⊢ φ →' ψ) (H₂ : Γ ⊢ ψ →' φ)  : Γ ⊢ (φ  ↔' ψ) :=
begin apply andI; assumption, end

def iffE_r {Γ} {φ ψ : formula L} (H : Γ ⊢ φ ↔' ψ)  : (Γ ⊢ φ →' ψ) := andE₁ _ H

def iffE_l {Γ} {φ ψ : formula L} (H : Γ ⊢ φ ↔' ψ)  : (Γ ⊢ ψ →' φ) := andE₂ _ H

/--
  Proof rule for eliminating the right part of a biconditional.
-/
def iffE₁ {Γ} {φ: formula L} (ψ : formula L) (H₁ : Γ ⊢ ψ) (H₂ : Γ ⊢ φ ↔' ψ)  : Γ ⊢ φ :=
begin
  apply impE ψ,
  { exact H₁, },
  { apply andE₂, exact H₂, },
end

/--
  Proof rule for eliminating the left part of a biconditional.
-/
def iffE₂ {Γ} (φ) {ψ : formula L} (H₁ : Γ ⊢ φ) (H₂ : Γ ⊢ φ ↔' ψ)  : (Γ ⊢  ψ) :=
begin
  apply impE φ,
  { exact H₁, },
  { apply andE₁, exact H₂, },
end

/--
  Proof rule for reflexivity of biconditionals.
-/
def iffI_refl {Γ} (φ : formula L) : Γ ⊢ (φ ↔' φ) := begin apply iffI; apply impI_refl,end
/--
  Proof rule for transitivity of biconditionals.
-/
def iffI_trans {Γ} {φ} (ψ: formula L) {χ}  (H₁: Γ ⊢ (φ ↔' ψ)) (H₂ : Γ ⊢ (ψ ↔' χ)) : Γ ⊢ (φ ↔' χ) :=
begin
    apply andI;
    apply impI_trans _ ψ _,
    apply andE₁ _ H₁, apply andE₁ _ H₂,
    apply andE₂ _ H₂, apply andE₂ _ H₁,
end
/--
  Proof rule for symmetry of biconditionals.
-/
def iffI_symm {Γ} {φ ψ: formula L}  (H: Γ ⊢ (φ ↔' ψ)) : Γ ⊢ (ψ ↔' φ) := 
begin apply iffI, apply andE₂, exact H, apply andE₁, exact H, end

-- rules for lifting and substitutions
/--
  Proof rule for substiuting a term for free variable .
-/
def substI {Γ} {φ : formula L} (t k) (H: Γ ⊢ φ ) : (λ ϕ, ϕ[t ⁄ k])'' Γ ⊢ φ[t ⁄ k] :=
begin
    induction H generalizing k,
    { apply hypI, exact mem_image_of_mem (λ (ϕ : preformula L 0), ϕ [t ⁄ k]) H_h, },
    { apply botE, apply H_ih, },

    { apply impI, rw ← (@image_insert_eq _ _ (λ (x : preformula L 0), x[t ⁄ k])), exact H_ih k, },
    { apply impE (H_φ [t ⁄ k]), exact H_ih_H₁ k, exact H_ih_H₂ k, },

    { apply andI, exact H_ih_H₁ k, exact H_ih_H₂ k, },
    { apply andE₁, exact H_ih k, },
    { apply andE₂, exact H_ih k, },

    { apply orI₁, exact H_ih k, },
    { apply orI₂, exact H_ih k, },
    { apply orE (H_φ [t ⁄ k]) (H_ψ [t ⁄ k]), 
      apply H_ih_H k, 
      have H₁:= H_ih_H₁ k, rw image_insert_eq at H₁, exact H₁,
      have H₂:= H_ih_H₂ k, rw image_insert_eq at H₂, exact H₂, },

    { apply allI, rw [image_image, lambda_lift_subst_formula(k.zero_le)], 
      have H := H_ih (k+1), rw image_image at H, exact H, },
    { apply allE' _ (H_t[t ⁄ k]) (H_ih k), apply subst_subst, exact (k.zero_le), },
  
    { apply exI (H_t [t⁄ k]), 
        have h:= subst_subst H_φ H_t t (k.zero_le), 
        rw nat.sub_zero at h, rw ←h, exact H_ih k,},
    { apply exE (H_φ [t⁄(k+1)]), apply H_ih_H₁ k, rw lift_subst H_ψ t 1 0 k (k.zero_le),
        have h:= H_ih_H₂ (k+1),
        rw [image_insert_eq, image_image, ←lambda_lift_subst_formula(k.zero_le)] at h,
        rw [image_image], exact h, },
    
    { apply eqI_refl, },
    { apply eqE', apply H_ih_H₁ k,
      have h:= H_ih_H₂ k, rwa [subst_subst H_φ H_s t (k.zero_le), nat.sub_zero] at h, 
      exact subst_subst H_φ H_t t (k.zero_le), }
end

/--
  Proof rule for introducing `m` fresh variables at index `i` to a proof.
-/
def liftI {Γ} {φ  : formula L} (m i : ℕ) (H: Γ ⊢ φ ) : (λ (ϕ :formula L), ϕ ↑ m ＠  i ) '' Γ ⊢ (φ ↑ m ＠  i) :=
begin
    induction H generalizing i,
    { apply hypI, exact mem_image_of_mem (λ (ϕ : preformula L 0),  ϕ ↑ m ＠  i) H_h, },
    { apply botE, exact H_ih i, },

    { apply impI, have:= H_ih i, rwa image_insert_eq at this, },
    { apply impE (H_φ ↑ m ＠  i) , exact H_ih_H₁ i, exact H_ih_H₂ i,},

    { apply andI, apply H_ih_H₁ i, apply H_ih_H₂ i, },
    { apply andE₁, apply H_ih i, },
    { apply andE₂, apply H_ih i, },

    { apply orI₁, apply H_ih i, },
    { apply orI₂, apply H_ih i, },
    { apply orE, apply H_ih_H i,
      have H₁:= H_ih_H₁ i, rw image_insert_eq at H₁, exact H₁,
      have H₂:= H_ih_H₂ i, rw image_insert_eq at H₂, exact H₂, },
    
    { apply allI, rw[image_image, lambda_lift_lift _ _ (i.zero_le)],
      have h:= H_ih (i+1), rw image_image at h, exact h, },
    { apply allE' _ (H_t ↑ m ＠ i) (H_ih i), 
      have h := eq.symm (subst_lift_in_lift H_φ H_t m i 0), exact h,},

    { apply exI (H_t ↑ m ＠ i), 
      rw subst0_lift_by_lift H_φ, 
      exact H_ih i,  },
    { apply exE (H_φ ↑ m ＠ (i+1)), apply H_ih_H₁ i, 
      rw[image_image, lift_lift H_ψ m 1 (i.zero_le), lambda_lift_lift _ _ (i.zero_le)],
      have h := H_ih_H₂ (i+1), rw[image_insert_eq, image_image] at h, exact h, },
    
    { apply eqI_refl, },
    { apply eqE' _ _ _ (H_ih_H₁ i),
      have h₁:= symm (subst0_lift_by_lift H_φ),
      have h₂ := H_ih_H₂ i, rw h₁ at h₂, exact h₂,
      exact symm ( subst0_lift_by_lift _ ), },
end


-- rules for dealing with universal closures
def allsI {Γ} {φ: formula L}  (n) (H: (λ ϕ , ϕ ↑ n ＠  0) '' Γ ⊢ φ) :  Γ ⊢ alls n φ  :=
begin
  induction n generalizing φ Γ,
  { simp [lift_by_0] at H, assumption,},
  { rw[alls], 
    apply allI,
    have h : (λ (ϕ : preformula L 0), ϕ ↑ n_n.succ ＠ 0) 
      = (λ (ϕ : preformula L 0), ϕ ↑ n_n ＠ 0) ∘ (λ (ϕ : preformula L 0), ϕ ↑ 1＠ 0),
    begin funext, dsimp, rw lift_at_lift_merge, rw add_comm 1 n_n, end,
    rw [h, image_comp] at H,
    exact n_ih H, },
end

def allsE  {Γ} {φ: formula L}  (n i) (H :  Γ ⊢ (alls n φ)) :  Γ ⊢ substs n i 0 φ :=
begin
  induction n generalizing φ i,
  { exact H,},
  { rw substs_succ, 
    apply allE, 
    rw all_substs, 
    rw [alls, all_alls] at H, 
    exact n_ih (i+1) H, },
end

def allsE' {Γ} (n) {φ  : formula L} (H : Γ ⊢ (alls n φ)) : (λ ϕ , ϕ ↑ n ＠  0) '' Γ ⊢ φ  :=
begin
  induction n generalizing φ Γ,
  { have h :  (λ (ϕ: formula L) , ϕ ↑ 0 ＠  0) = id, from begin funext, rw lift_by_0, refl, end,
    rw [h, image_id] at *, 
    rwa alls at H, },
  { have h: (λ (ϕ : preformula L 0), ϕ ↑ n_n.succ ＠ 0) 
          = (λ (ϕ : preformula L 0), ϕ ↑ 1 ＠ 0) ∘ (λ (ϕ : preformula L 0), ϕ ↑ n_n ＠ 0),
    begin funext, dsimp, rw lift_at_lift_merge, end,
    rw [alls_succ] at H,
    apply allE_var0,
    rw [h,image_comp],
    apply liftI, 
    exact n_ih H, },
end

def modus_tollens {Γ} {φ} (ψ: formula L) (H₁: Γ ⊢ (φ →' ψ)) (H₂: Γ ⊢ ¬'ψ) : Γ ⊢ ¬'φ  :=
begin
  apply impI,
  apply impE ψ,
  { apply impE_insert,
   assumption, },
  { apply weak1,
    assumption, },
end
end proof

export proof

/--
  Formal proof that there always exists an object of discourse,
-/
def let_there_be_light : (∅ : set $ formula L) ⊢ ∃'(#0 =' #0) :=
begin
  apply exI #0,
  apply eqI,
end

/- Two variants of
  "All men are mortal.
   Socrates is a man.
   Therefore, Socrates is mortal." .   
-/

example {Γ:set $ formula L}{φ ψ χ}  (H₁: Γ ⊢ ∀'(φ →' ψ))  (H₂: Γ ⊢ ∀'(ψ →' χ)) : Γ ⊢ ∀' (φ →' χ) :=
begin
  apply allI,
  apply impI,
  apply impE ψ,
  { apply impE_insert,
    apply allE' ((φ →' ψ) ↑ 1 ＠  1) #0,
    rw ←formula.lift,
    apply liftI,
    exact H₁,
    rw subst_var0_lift_by_1, },
  { apply weak1,
    apply allE' ((ψ →' χ) ↑ 1 ＠  1) #0,
    rw ←formula.lift,
    apply liftI,
    exact H₂,
    rw subst_var0_lift_by_1, },
end

example {Γ:set $ formula L}{φ ψ χ}  (H₁: Γ ⊢ ∀'(φ →' ψ) )  (H₂: Γ ⊢ ∀'(ψ →' χ)) : Γ ⊢ ∀' (φ →' χ) :=
begin
  apply allI,
  apply impI,
  apply impE ψ,
  apply impE_insert,
  swap,
  apply weak1,
  all_goals 
  { apply allE' ( _ ↑ 1 ＠  1) #0,
    rw ←formula.lift,
    apply liftI,
    swap,
    rw subst_var0_lift_by_1,
    assumption, },
end
end fol