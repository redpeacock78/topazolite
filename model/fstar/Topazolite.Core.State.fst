module Topazolite.Core.State

open FStar.List.Tot

type token = nat
type name = string

type term =
  | Opaque : ts:list token -> term
  | Resource : n:nat -> term
  | OwnedLeaf : tk:token -> v:term -> term
  | OwnedTransit : p:nat -> v:term -> term
  | PrimVal : o:name -> op:name -> term
  | Var : x:name -> term
  | Apply : cs:list term -> term
  | Let : x:name -> ty:name -> rhs:term -> body:term -> term
  | Construct : ty:name -> k:name -> cs:list term -> term
  | Rec : fs:list (name & name & term) -> term
  | OwnLeaf : c:term -> term
  | Scope : pi:name -> c:term -> term

let rec is_value (t:term) : Tot bool (decreases t) =
  match t with
  | Opaque _ -> true
  | Resource _ -> true
  | OwnedLeaf _ v -> is_value v
  | OwnedTransit _ v -> is_value v
  | PrimVal _ _ -> true
  | Var _ -> false
  | Apply _ -> false
  | Let _ _ _ _ -> false
  | Construct _ _ cs -> all_values cs
  | Rec fs -> all_record_values fs
  | OwnLeaf _ -> false
  | Scope _ _ -> false
and all_values (ts:list term) : Tot bool (decreases ts) =
  match ts with
  | [] -> true
  | t :: rest -> is_value t && all_values rest
and all_record_values (fs:list (name & name & term)) : Tot bool (decreases fs) =
  match fs with
  | [] -> true
  | (_, _, v) :: rest -> is_value v && all_record_values rest

type value = v:term{is_value v}

let value_to_term (v:value) : term = v

let value_field_to_term (f:name & name & value) : name & name & term =
  match f with
  | (label, mode, v) -> (label, mode, value_to_term v)

type ctx =
  | EHole : ctx
  | EApply : vs:list value -> e:ctx -> cs:list term -> ctx
  | ELet : x:name -> ty:name -> e:ctx -> body:term -> ctx
  | EConstruct : ty:name -> k:name -> vs:list value -> e:ctx -> cs:list term -> ctx
  | ERec : vfs:list (name & name & value) -> l:name -> m:name -> e:ctx
           -> cfs:list (name & name & term) -> ctx
  | EOwnLeaf : e:ctx -> ctx
  | EScope : pi:name -> e:ctx -> ctx

let rec plug (e:ctx) (r:term) : Tot term (decreases e) =
  match e with
  | EHole -> r
  | EApply vs e cs ->
      Apply (append (map value_to_term vs) (plug e r :: cs))
  | ELet x ty e body -> Let x ty (plug e r) body
  | EConstruct ty k vs e cs ->
      Construct ty k
        (append (map value_to_term vs) (plug e r :: cs))
  | ERec vfs l m e cfs ->
      Rec (append
             (map value_field_to_term vfs)
             ((l, m, plug e r) :: cfs))
  | EOwnLeaf e -> OwnLeaf (plug e r)
  | EScope pi e -> Scope pi (plug e r)

type tok_state = | Available | Moved | Observed | Dropped
type root_state = | RAvailable | RMoved | RDropped

noeq type state = {
  control : term;
  heap : list (nat & term);
  roots : list (nat & root_state);
  ledger : list (token & tok_state);
  trace : list term
}
