open tactic interactive interactive.types

namespace tactic
namespace interactive

/- apply followed by simp with tls. not yet useful -/
meta def sapply (q : parse texpr) : tactic unit :=
  concat_tags (do h ← i_to_expr_for_apply q, tactic.apply h) 
  >> (simp none none ff {} {"tls"} (loc.ns [none]) )

end interactive
end tactic