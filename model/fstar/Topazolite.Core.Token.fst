module Topazolite.Core.Token

open FStar.List.Tot
open FStar.List.Tot.Properties
open Topazolite.Core.State

let rec term_size (t:term) : Tot nat (decreases t) =
  match t with
  | OwnedLeaf _ v -> 1 + term_size v
  | OwnedTransit _ v -> 1 + term_size v
  | Apply cs -> 1 + terms_size cs
  | Let _ _ rhs body -> 1 + term_size rhs + term_size body
  | Construct _ _ cs -> 1 + terms_size cs
  | Rec fs -> 1 + fields_size fs
  | OwnLeaf c -> 1 + term_size c
  | Scope _ c -> 1 + term_size c
  | _ -> 1
and terms_size (ts:list term) : Tot nat (decreases ts) =
  match ts with
  | [] -> 0
  | t :: rest -> term_size t + 1 + terms_size rest
and fields_size (fs:list (name & name & term)) : Tot nat (decreases fs) =
  match fs with
  | [] -> 0
  | (_, _, t) :: rest -> term_size t + 1 + fields_size rest

let rec collect_tokens (t:term) : Tot (list token) (decreases (term_size t)) =
  match t with
  | OwnedLeaf tk v -> tk :: collect_tokens v
  | OwnedTransit _ v -> collect_tokens v
  | Apply cs -> collect_terms cs
  | Let _ _ rhs body -> collect_tokens rhs @ collect_tokens body
  | Construct _ _ cs -> collect_terms cs
  | Rec fs -> collect_fields fs
  | OwnLeaf c -> collect_tokens c
  | Scope _ c -> collect_tokens c
  | _ -> []
and collect_terms (ts:list term)
  : Tot (list token) (decreases (terms_size ts)) =
  match ts with
  | [] -> []
  | t :: rest -> collect_tokens t @ collect_terms rest
and collect_fields (fs:list (name & name & term))
  : Tot (list token) (decreases (fields_size fs)) =
  match fs with
  | [] -> []
  | (_, _, t) :: rest -> collect_tokens t @ collect_fields rest

let rec collect_values (vs:list value) : Tot (list token) (decreases vs) =
  match vs with
  | [] -> []
  | v :: rest -> collect_tokens (value_to_term v) @ collect_values rest

let rec ctx_tokens (e:ctx) : Tot (list token) (decreases e) =
  match e with
  | EHole -> []
  | EApply vs inner cs ->
      collect_terms (map value_to_term vs) @ ctx_tokens inner @ collect_terms cs
  | ELet _ _ inner body -> ctx_tokens inner @ collect_tokens body
  | EConstruct _ _ vs inner cs ->
      collect_terms (map value_to_term vs) @ ctx_tokens inner @ collect_terms cs
  | ERec vfs _ _ inner cfs ->
      collect_fields (map value_field_to_term vfs) @
      ctx_tokens inner @ collect_fields cfs
  | EOwnLeaf inner -> ctx_tokens inner
  | EScope _ inner -> ctx_tokens inner

//@ AUX: helper THM-008
let rec collect_terms_append (xs:list term) (ys:list term)
  : Lemma (ensures collect_terms (xs @ ys) =
                    collect_terms xs @ collect_terms ys)
    (decreases (terms_size xs)) =
  match xs with
  | [] -> ()
  | head :: rest ->
      append_cons_l head rest ys;
      collect_terms_append rest ys;
      append_assoc (collect_tokens head) (collect_terms rest)
        (collect_terms ys);
      assert (collect_terms (xs @ ys) =
              collect_tokens head @ collect_terms (rest @ ys));
      assert (collect_terms xs =
              collect_tokens head @ collect_terms rest)

//@ AUX: helper THM-008
let collect_terms_append_count (tk:token) (xs:list term) (ys:list term)
  : Lemma (ensures count tk (collect_terms (xs @ ys)) =
                    count tk (collect_terms xs) +
                    count tk (collect_terms ys)) =
  collect_terms_append xs ys;
  append_count (collect_terms xs) (collect_terms ys) tk

//@ AUX: helper THM-008
let rec collect_fields_append (xs:list (name & name & term))
  (ys:list (name & name & term))
  : Lemma (ensures collect_fields (xs @ ys) =
                    collect_fields xs @ collect_fields ys)
    (decreases (fields_size xs)) =
  match xs with
  | [] -> ()
  | (label, mode, head) :: rest ->
      append_cons_l (label, mode, head) rest ys;
      collect_fields_append rest ys;
      append_assoc (collect_tokens head) (collect_fields rest)
        (collect_fields ys);
      assert (collect_fields (xs @ ys) =
              collect_tokens head @ collect_fields (rest @ ys));
      assert (collect_fields xs =
              collect_tokens head @ collect_fields rest)

//@ AUX: helper THM-008
let collect_fields_append_count (tk:token)
  (xs:list (name & name & term)) (ys:list (name & name & term))
  : Lemma (ensures count tk (collect_fields (xs @ ys)) =
                    count tk (collect_fields xs) +
                    count tk (collect_fields ys)) =
  collect_fields_append xs ys;
  append_count (collect_fields xs) (collect_fields ys) tk

//@ AUX: helper THM-008
let rec plug_tokens (e:ctx) (r:term) : Lemma
  (ensures forall (tk:token).
    count tk (collect_tokens (plug e r)) =
    count tk (ctx_tokens e) + count tk (collect_tokens r))
  (decreases e) =
  match e with
  | EHole -> ()
  | EApply vs inner cs ->
      plug_tokens inner r;
      let prefix = map value_to_term vs in
      let aux (tk:token) : Lemma
        (ensures count tk (collect_tokens (plug e r)) =
          count tk (ctx_tokens e) + count tk (collect_tokens r)) =
        collect_terms_append_count tk prefix (plug inner r :: cs);
        append_count (collect_tokens (plug inner r)) (collect_terms cs) tk;
        append_count (collect_terms prefix)
          (ctx_tokens inner @ collect_terms cs) tk;
        append_count (ctx_tokens inner) (collect_terms cs) tk
      in FStar.Classical.forall_intro aux
  | ELet x ty inner body ->
      plug_tokens inner r;
      let aux (tk:token) : Lemma
        (ensures count tk (collect_tokens (plug e r)) =
          count tk (ctx_tokens e) + count tk (collect_tokens r)) =
        append_count (collect_tokens (plug inner r))
          (collect_tokens body) tk;
        append_count (ctx_tokens inner) (collect_tokens body) tk
      in FStar.Classical.forall_intro aux
  | EConstruct ty k vs inner cs ->
      plug_tokens inner r;
      let prefix = map value_to_term vs in
      let aux (tk:token) : Lemma
        (ensures count tk (collect_tokens (plug e r)) =
          count tk (ctx_tokens e) + count tk (collect_tokens r)) =
        collect_terms_append_count tk prefix (plug inner r :: cs);
        append_count (collect_tokens (plug inner r)) (collect_terms cs) tk;
        append_count (collect_terms prefix)
          (ctx_tokens inner @ collect_terms cs) tk;
        append_count (ctx_tokens inner) (collect_terms cs) tk
      in FStar.Classical.forall_intro aux
  | ERec vfs l m inner cfs ->
      plug_tokens inner r;
      let prefix = map value_field_to_term vfs in
      let hole = [(l, m, plug inner r)] in
      let aux (tk:token) : Lemma
        (ensures count tk (collect_tokens (plug e r)) =
          count tk (ctx_tokens e) + count tk (collect_tokens r)) =
        collect_fields_append_count tk prefix (hole @ cfs);
        append_count (collect_fields hole) (collect_fields cfs) tk;
        append_assoc (collect_fields prefix) (ctx_tokens inner)
          (collect_fields cfs);
        append_count (collect_fields prefix @ ctx_tokens inner)
          (collect_fields cfs) tk;
        append_count (collect_fields prefix) (ctx_tokens inner) tk
      in FStar.Classical.forall_intro aux
  | EOwnLeaf inner -> plug_tokens inner r
  | EScope pi inner -> plug_tokens inner r

//@ AUX: helper THM-008
let rec collect_terms_replace (prefix:list term) (left right:term)
  (suffix:list term)
  : Lemma
      (requires collect_tokens left = collect_tokens right)
      (ensures collect_terms (prefix @ (left :: suffix)) =
               collect_terms (prefix @ (right :: suffix)))
  (decreases (terms_size prefix)) =
  match prefix with
  | [] -> ()
  | head :: rest ->
      collect_terms_append (head :: rest) (left :: suffix);
      collect_terms_append (head :: rest) (right :: suffix);
      collect_terms_replace rest left right suffix;
      assert (collect_terms (prefix @ (left :: suffix)) =
              collect_tokens head @ collect_terms (rest @ (left :: suffix)));
      assert (collect_terms (prefix @ (right :: suffix)) =
              collect_tokens head @ collect_terms (rest @ (right :: suffix)))

//@ AUX: helper THM-008
let rec collect_fields_replace (prefix:list (name & name & term))
  (label:name) (mode:name) (left right:term)
  (suffix:list (name & name & term))
  : Lemma
      (requires collect_tokens left = collect_tokens right)
      (ensures collect_fields (prefix @ ((label, mode, left) :: suffix)) =
               collect_fields (prefix @ ((label, mode, right) :: suffix)))
  (decreases (fields_size prefix)) =
  match prefix with
  | [] -> ()
  | (head_label, head_mode, head) :: rest ->
      collect_fields_append
        ((head_label, head_mode, head) :: rest)
        ((label, mode, left) :: suffix);
      collect_fields_append
        ((head_label, head_mode, head) :: rest)
        ((label, mode, right) :: suffix);
      collect_fields_replace rest label mode left right suffix;
      assert (collect_fields
                (prefix @ ((label, mode, left) :: suffix)) =
              collect_tokens head @
                collect_fields (rest @ ((label, mode, left) :: suffix)));
      assert (collect_fields
                (prefix @ ((label, mode, right) :: suffix)) =
              collect_tokens head @
                collect_fields (rest @ ((label, mode, right) :: suffix)))

//@ AUX: helper THM-008
let rec plug_tokens_congruent (e:ctx) (left right:term) : Lemma
  (requires collect_tokens left = collect_tokens right)
  (ensures collect_tokens (plug e left) = collect_tokens (plug e right))
  (decreases e) =
  match e with
  | EHole -> ()
  | EApply vs inner cs ->
      plug_tokens_congruent inner left right;
      let prefix = map value_to_term vs in
      collect_terms_replace prefix (plug inner left) (plug inner right) cs
  | ELet x ty inner body ->
      plug_tokens_congruent inner left right;
      assert (collect_tokens (plug e left) =
              collect_tokens (plug inner left) @ collect_tokens body);
      assert (collect_tokens (plug e right) =
              collect_tokens (plug inner right) @ collect_tokens body)
  | EConstruct ty k vs inner cs ->
      plug_tokens_congruent inner left right;
      let prefix = map value_to_term vs in
      collect_terms_replace prefix (plug inner left) (plug inner right) cs
  | ERec vfs label mode inner cfs ->
      plug_tokens_congruent inner left right;
      let prefix = map value_field_to_term vfs in
      collect_fields_replace prefix label mode
        (plug inner left) (plug inner right) cfs
  | EOwnLeaf inner -> plug_tokens_congruent inner left right
  | EScope pi inner -> plug_tokens_congruent inner left right

let rec heap_tokens (heap:list (nat & term)) : Tot (list token) (decreases heap) =
  match heap with
  | [] -> []
  | (_, value) :: rest -> collect_tokens value @ heap_tokens rest

let rec root_available (place:nat) (roots:list (nat & root_state))
  : Tot bool (decreases roots) =
  match roots with
  | [] -> false
  | (p, status) :: rest ->
      if p = place then status = RAvailable else root_available place rest

let rec heap_value (place:nat) (heap:list (nat & term))
  : Tot (option term) (decreases heap) =
  match heap with
  | [] -> None
  | (p, value) :: rest -> if p = place then Some value else heap_value place rest

let rec available_root_values (heap:list (nat & term))
  (roots:list (nat & root_state)) : Tot (list term) (decreases roots) =
  match roots with
  | [] -> []
  | (place, status) :: rest ->
      let tail = available_root_values heap rest in
      if status = RAvailable then
        match heap_value place heap with
        | Some value -> value :: tail
        | None -> tail
      else tail

let rec collect_term_values (vs:list term) : Tot (list token) (decreases vs) =
  match vs with
  | [] -> []
  | value :: rest -> collect_tokens value @ collect_term_values rest

let structural_tokens (s:state) : list token =
  collect_tokens s.control @
  collect_term_values (available_root_values s.heap s.roots)

let observed_tokens (s:state) : list token = collect_terms s.trace

let rec ledger_keys (entries:list (token & tok_state))
  : Tot (list token) (decreases entries) =
  match entries with
  | [] -> []
  | (tk, _) :: rest -> tk :: ledger_keys rest

let rec ledger_status (tk:token) (entries:list (token & tok_state))
  : Tot (option tok_state) (decreases entries) =
  match entries with
  | [] -> None
  | (key, status) :: rest ->
      if tk = key then Some status else ledger_status tk rest

let rec ledger_contains (tk:token) (entries:list (token & tok_state))
  : Tot bool (decreases entries) =
  match entries with
  | [] -> false
  | (key, _) :: rest -> tk = key || ledger_contains tk rest

let unique_counts (tokens:list token) : GTot bool =
  forall (tk:token). count tk tokens <= 1

let tokens_registered (structural:list token) (observed:list token)
  (entries:list (token & tok_state)) : GTot bool =
  forall (tk:token).
    ((count tk structural > 0 || count tk observed > 0) ==>
     ledger_contains tk entries)

let disjoint_tokens (left:list token) (right:list token) : GTot bool =
  forall (tk:token). count tk left = 0 || count tk right = 0

let ledger_entries_valid
  (structural:list token) (observed:list token)
  (entries:list (token & tok_state)) : GTot bool =
  forall (tk:token).
    (match ledger_status tk entries with
     | None -> true
     | Some status ->
         let in_structural = count tk structural in
         let in_observed = count tk observed in
         match status with
         | Available | Moved -> in_structural = 1 && in_observed = 0
         | Observed -> in_structural = 0 && in_observed = 1
         | Dropped -> in_structural = 0 && in_observed <= 1)

let tok_inv (s:state) : GTot bool =
  let structural = structural_tokens s in
  let observed = observed_tokens s in
  unique_counts structural && unique_counts observed &&
  unique_counts (ledger_keys s.ledger) &&
  disjoint_tokens structural observed &&
  tokens_registered structural observed s.ledger &&
  ledger_entries_valid structural observed s.ledger

let rec fresh_heap (tk:token) (heap:list (nat & term))
  : Tot bool (decreases heap) =
  match heap with
  | [] -> true
  | (_, value) :: rest ->
      not (mem tk (collect_tokens value)) && fresh_heap tk rest

let fresh_in (s:state) (tk:token) : bool =
  not (mem tk (collect_tokens s.control)) &&
  fresh_heap tk s.heap &&
  not (mem tk (collect_terms s.trace)) &&
  not (mem tk (structural_tokens s)) &&
  not (mem tk (observed_tokens s)) &&
  not (mem tk (ledger_keys s.ledger))

let is_delta_acquire (r:term) : bool =
  match r with
  | Apply [PrimVal _ "acquire"; Resource _] -> true
  | _ -> false

let step_delta_acquire (e:ctx) (r:term{is_delta_acquire r})
  (s:state{s.control = plug e r}) (tk:token{fresh_in s tk}) : Tot state =
  match r with
  | Apply [PrimVal _ "acquire"; Resource n] ->
      { s with
        control = plug e (OwnedLeaf tk (Resource n));
        ledger = (tk, Available) :: s.ledger }
  | _ -> s

let step_ownleaf (e:ctx) (v:value{not (match v with OwnedLeaf _ _ | OwnedTransit _ _ -> true | _ -> false)})
  (s:state{s.control = plug e (OwnLeaf v)}) (tk:token{fresh_in s tk}) : Tot state =
  { s with
    control = plug e (OwnedLeaf tk v);
    ledger = (tk, Available) :: s.ledger }

let step_ownleaf_pass (e:ctx) (tk:token) (v:value)
  (s:state{s.control = plug e (OwnLeaf (OwnedLeaf tk v))}) : Tot state =
  { s with control = plug e (OwnedLeaf tk v) }

let step_ownleaf_transit (e:ctx) (place:nat) (v:value)
  (s:state{s.control = plug e (OwnLeaf (OwnedTransit place v))}) : Tot state =
  { s with control = plug e (OwnedTransit place v) }

let fresh_update (s:state) (control:term) (tk:token) : state =
  { s with control = control; ledger = (tk, Available) :: s.ledger }

//@ AUX: helper THM-008
let fresh_token_count_update (e:ctx) (before after:term) (tk:token)
  (rest:list token) (x:token) : Lemma
  (requires (collect_tokens before = rest /\
             collect_tokens after = tk :: rest))
  (ensures count x (collect_tokens (plug e after)) =
           count x (collect_tokens (plug e before)) +
             (if x = tk then 1 else 0)) =
  plug_tokens e after;
  plug_tokens e before;
  append_count (collect_tokens after) (ctx_tokens e) x;
  append_count (collect_tokens before) (ctx_tokens e) x;
  assert (count x (collect_tokens after) =
          count x rest + (if x = tk then 1 else 0));
  assert (count x (collect_tokens before) = count x rest)

//@ AUX: helper THM-008
let delta_acquire_count_update (e:ctx) (b:name) (n:nat) (s:state)
  (tk:token{fresh_in s tk}) (x:token) : Lemma
  (requires (s.control =
               plug e (Apply [PrimVal b "acquire"; Resource n])))
  (ensures count x (collect_tokens (plug e (OwnedLeaf tk (Resource n)))) =
           count x (collect_tokens s.control) +
             (if x = tk then 1 else 0)) =
  assert (collect_tokens (Apply [PrimVal b "acquire"; Resource n]) = []);
  assert (collect_tokens (OwnedLeaf tk (Resource n)) = [tk]);
  fresh_token_count_update e
    (Apply [PrimVal b "acquire"; Resource n])
    (OwnedLeaf tk (Resource n)) tk [] x;
  assert (s.control =
          plug e (Apply [PrimVal b "acquire"; Resource n]));
  assert (count x (collect_tokens (plug e (OwnedLeaf tk (Resource n)))) =
          count x (collect_tokens s.control) +
            (if x = tk then 1 else 0))

//@ AUX: helper THM-008
let fresh_update_structural_count (s:state) (control:term) (tk:token)
  (count_update:(x:token) -> Lemma
    (ensures count x (collect_tokens control) =
      count x (collect_tokens s.control) + (if x = tk then 1 else 0)))
  (x:token) : Lemma
  (ensures count x (structural_tokens (fresh_update s control tk)) =
    count x (structural_tokens s) + (if x = tk then 1 else 0)) =
  count_update x;
  append_count (collect_tokens s.control)
    (collect_term_values (available_root_values s.heap s.roots)) x;
  append_count (collect_tokens control)
    (collect_term_values (available_root_values s.heap s.roots)) x

//@ AUX: helper THM-008
let fresh_update_unique_structural (s:state) (control:term)
  (tk:token{fresh_in s tk})
  (count_update:(x:token) -> Lemma
    (ensures count x (collect_tokens control) =
      count x (collect_tokens s.control) + (if x = tk then 1 else 0)))
  : Lemma (requires tok_inv s)
          (ensures unique_counts (structural_tokens (fresh_update s control tk))) =
  let next = fresh_update s control tk in
  let old_structural = structural_tokens s in
  let prove_count (x:token) : Lemma
    (ensures count x (structural_tokens next) <= 1) =
    fresh_update_structural_count s control tk count_update x;
    if x = tk then
      (mem_count old_structural tk;
       assert (not (mem tk old_structural));
       assert (count x old_structural = 0))
    else
      assert (count x (structural_tokens next) = count x old_structural);
    assert (count x old_structural <= 1)
  in
  FStar.Classical.forall_intro prove_count

//@ AUX: helper THM-008
let fresh_update_unique_keys (s:state) (control:term)
  (tk:token{fresh_in s tk})
  (count_update:(x:token) -> Lemma
    (ensures count x (collect_tokens control) =
      count x (collect_tokens s.control) + (if x = tk then 1 else 0)))
  : Lemma (requires tok_inv s)
          (ensures unique_counts (ledger_keys (fresh_update s control tk).ledger)) =
  let old_keys = ledger_keys s.ledger in
  let new_keys = ledger_keys (fresh_update s control tk).ledger in
  let prove_count (x:token) : Lemma (ensures count x new_keys <= 1) =
    assert (count x new_keys = (if x = tk then 1 else 0) + count x old_keys);
    if x = tk then
      (mem_count old_keys tk;
       assert (not (mem tk old_keys));
       assert (count x old_keys = 0))
    else
      assert (count x new_keys = count x old_keys);
    assert (count x old_keys <= 1)
  in
  FStar.Classical.forall_intro prove_count

//@ AUX: helper THM-008
let fresh_update_disjoint (s:state) (control:term)
  (tk:token{fresh_in s tk})
  (count_update:(x:token) -> Lemma
    (ensures count x (collect_tokens control) =
      count x (collect_tokens s.control) + (if x = tk then 1 else 0)))
  : Lemma (requires tok_inv s)
          (ensures disjoint_tokens
            (structural_tokens (fresh_update s control tk)) (observed_tokens s)) =
  let prove_count (x:token) : Lemma
    (ensures count x (structural_tokens (fresh_update s control tk)) = 0 ||
             count x (observed_tokens s) = 0) =
    fresh_update_structural_count s control tk count_update x;
    if x = tk then
      (mem_count (observed_tokens s) tk;
       assert (not (mem tk (observed_tokens s)));
       assert (count x (observed_tokens s) = 0))
    else
      (assert (count x (structural_tokens (fresh_update s control tk)) =
               count x (structural_tokens s));
       assert (count x (structural_tokens s) = 0 ||
               count x (observed_tokens s) = 0))
  in
  FStar.Classical.forall_intro prove_count

//@ AUX: helper THM-008
let fresh_update_registered (s:state) (control:term)
  (tk:token{fresh_in s tk})
  (count_update:(x:token) -> Lemma
    (ensures count x (collect_tokens control) =
      count x (collect_tokens s.control) + (if x = tk then 1 else 0)))
  : Lemma (requires tok_inv s)
          (ensures tokens_registered
            (structural_tokens (fresh_update s control tk)) (observed_tokens s)
            (fresh_update s control tk).ledger) =
  let prove_count (x:token) : Lemma
    (ensures ((count x (structural_tokens (fresh_update s control tk)) > 0 ||
               count x (observed_tokens s) > 0) ==>
              ledger_contains x (fresh_update s control tk).ledger)) =
    fresh_update_structural_count s control tk count_update x;
    if x = tk then
      (assert (ledger_contains x (fresh_update s control tk).ledger))
    else
      (assert (count x (structural_tokens (fresh_update s control tk)) =
               count x (structural_tokens s));
       assert ((count x (structural_tokens s) > 0 ||
                count x (observed_tokens s) > 0) ==> ledger_contains x s.ledger);
       assert (ledger_contains x (fresh_update s control tk).ledger =
               ledger_contains x s.ledger);
       assert ((count x (structural_tokens (fresh_update s control tk)) > 0 ||
                count x (observed_tokens s) > 0) ==>
               ledger_contains x (fresh_update s control tk).ledger))
  in
  FStar.Classical.forall_intro prove_count

//@ AUX: helper THM-008
let fresh_update_ledger_entries_valid (s:state) (control:term)
  (tk:token{fresh_in s tk})
  (count_update:(x:token) -> Lemma
    (ensures count x (collect_tokens control) =
      count x (collect_tokens s.control) + (if x = tk then 1 else 0)))
  : Lemma (requires tok_inv s)
          (ensures ledger_entries_valid
            (structural_tokens (fresh_update s control tk)) (observed_tokens s)
            (fresh_update s control tk).ledger) =
  let old_structural = structural_tokens s in
  let observed = observed_tokens s in
  let next = fresh_update s control tk in
  let prove_entry (x:token) : Lemma
    (ensures (match ledger_status x next.ledger with
      | None -> true
      | Some status ->
          let in_structural = count x (structural_tokens next) in
          let in_observed = count x observed in
          match status with
          | Available | Moved -> in_structural = 1 && in_observed = 0
          | Observed -> in_structural = 0 && in_observed = 1
          | Dropped -> in_structural = 0 && in_observed <= 1)) =
    fresh_update_structural_count s control tk count_update x;
    if x = tk then
      (mem_count old_structural tk;
       assert (not (mem tk old_structural));
       assert (count x old_structural = 0);
       mem_count observed tk;
       assert (not (mem tk observed));
       assert (count x (structural_tokens next) = 1);
       assert (count x observed = 0))
    else
      (assert (ledger_status x next.ledger = ledger_status x s.ledger);
       assert (count x (structural_tokens next) = count x old_structural);
       assert (match ledger_status x s.ledger with
         | None -> true
         | Some status ->
             let in_structural = count x old_structural in
             let in_observed = count x observed in
             match status with
             | Available | Moved -> in_structural = 1 && in_observed = 0
             | Observed -> in_structural = 0 && in_observed = 1
             | Dropped -> in_structural = 0 && in_observed <= 1))
  in
  FStar.Classical.forall_intro prove_entry

//@ AUX: helper THM-008
let fresh_update_preserves_tok_inv (s:state) (control:term)
  (tk:token{fresh_in s tk})
  (count_update:(x:token) -> Lemma
    (ensures count x (collect_tokens control) =
      count x (collect_tokens s.control) + (if x = tk then 1 else 0)))
  : Lemma (requires tok_inv s)
          (ensures tok_inv (fresh_update s control tk)) =
  fresh_update_unique_structural s control tk count_update;
  fresh_update_unique_keys s control tk count_update;
  fresh_update_disjoint s control tk count_update;
  fresh_update_registered s control tk count_update;
  fresh_update_ledger_entries_valid s control tk count_update;
  assert (unique_counts (observed_tokens (fresh_update s control tk)) =
          unique_counts (observed_tokens s));
  assert (tok_inv (fresh_update s control tk))

//@ THM: THM-008
//@ REQ-FULL: -
//@ REQ-PART: OWN-009
//@ SPEC: core-calculus.md §5.1, core-calculus.md §5.3
//@ RULE: R-Delta, R-OwnLeaf, R-OwnLeafPass, R-OwnLeafTransit
//@ REDEX: model/redex/tests/root-token-test.rkt
//@ ASSUMPTIONS: tok_inv
//@ SCOPE: R-Delta（acquire）の遷移について、新しい token は遷移の定義域の精緻型で選ぶものとし、評価文脈は七つの構成子に限る
let delta_acquire_preserves_tok_inv (e:ctx) (r:term) (s:state)
  (tk:token{fresh_in s tk})
  : Lemma
      (requires (tok_inv s /\ s.control = plug e r /\ is_delta_acquire r))
      (ensures (tok_inv (step_delta_acquire e r s tk))) =
  match r with
  | Apply [PrimVal b "acquire"; Resource n] ->
      let control = plug e (OwnedLeaf tk (Resource n)) in
      let count_update (x:token) : Lemma
        (ensures count x (collect_tokens control) =
          count x (collect_tokens s.control) + (if x = tk then 1 else 0)) =
        assert (s.control =
                plug e (Apply [PrimVal b "acquire"; Resource n]));
        delta_acquire_count_update e b n s tk x;
        assert (s.control = plug e r);
        assert (count x (collect_tokens control) =
                count x (collect_tokens s.control) +
                  (if x = tk then 1 else 0))
      in
      fresh_update_preserves_tok_inv s control tk count_update;
      assert (tok_inv (step_delta_acquire e r s tk))
  | _ -> ()

//@ THM: THM-008
//@ REQ-FULL: -
//@ REQ-PART: OWN-009
//@ SPEC: core-calculus.md §5.1, core-calculus.md §5.3
//@ RULE: R-Delta, R-OwnLeaf, R-OwnLeafPass, R-OwnLeafTransit
//@ REDEX: model/redex/tests/root-token-test.rkt
//@ ASSUMPTIONS: tok_inv
//@ SCOPE: R-OwnLeaf の遷移について、新しい token は遷移の定義域の精緻型で選ぶものとし、評価文脈は七つの構成子に限る
let ownleaf_preserves_tok_inv (e:ctx) (v:value) (s:state)
  (tk:token{fresh_in s tk})
  : Lemma
      (requires (tok_inv s /\
                 s.control = plug e (OwnLeaf v) /\
                 not (match v with OwnedLeaf _ _ | OwnedTransit _ _ -> true | _ -> false)))
      (ensures (tok_inv (step_ownleaf e v s tk))) =
  let control = plug e (OwnedLeaf tk (value_to_term v)) in
  let count_update (x:token) : Lemma
    (ensures count x (collect_tokens control) =
      count x (collect_tokens s.control) + (if x = tk then 1 else 0)) =
    let before = OwnLeaf (value_to_term v) in
    let after = OwnedLeaf tk (value_to_term v) in
    assert (collect_tokens before = collect_tokens (value_to_term v));
    assert (collect_tokens after = tk :: collect_tokens (value_to_term v));
    fresh_token_count_update e before after tk
      (collect_tokens (value_to_term v)) x;
    assert (control = plug e after);
    assert (s.control = plug e before);
    assert (count x (collect_tokens control) =
            count x (collect_tokens s.control) +
              (if x = tk then 1 else 0))
  in
  fresh_update_preserves_tok_inv s control tk count_update;
  assert (tok_inv (step_ownleaf e v s tk))

//@ AUX: helper THM-008
let ownleaf_pass_preserves_token_list (e:ctx) (tk:token) (v:value) (s:state)
  : Lemma
      (requires s.control = plug e (OwnLeaf (OwnedLeaf tk v)))
      (ensures collect_tokens (step_ownleaf_pass e tk v s).control =
               collect_tokens s.control) =
  let before = OwnLeaf (OwnedLeaf tk v) in
  let after = OwnedLeaf tk v in
  assert (collect_tokens before = collect_tokens after);
  plug_tokens_congruent e after before;
  assert (step_ownleaf_pass e tk v s).control = plug e after;
  assert s.control = plug e before

//@ THM: THM-008
//@ REQ-FULL: -
//@ REQ-PART: OWN-009
//@ SPEC: core-calculus.md §5.1, core-calculus.md §5.3
//@ RULE: R-Delta, R-OwnLeaf, R-OwnLeafPass, R-OwnLeafTransit
//@ REDEX: model/redex/tests/root-token-test.rkt
//@ ASSUMPTIONS: tok_inv
//@ SCOPE: R-OwnLeafPass の遷移について、評価文脈は七つの構成子に限る
let ownleaf_pass_preserves_tok_inv (e:ctx) (tk:token) (v:value) (s:state)
  : Lemma
      (requires (tok_inv s /\
                 s.control = plug e (OwnLeaf (OwnedLeaf tk v))))
      (ensures (tok_inv (step_ownleaf_pass e tk v s))) =
  ownleaf_pass_preserves_token_list e tk v s;
  assert (tok_inv (step_ownleaf_pass e tk v s))

//@ AUX: helper THM-008
let ownleaf_transit_preserves_token_list (e:ctx) (place:nat) (v:value) (s:state)
  : Lemma
      (requires s.control = plug e (OwnLeaf (OwnedTransit place v)))
      (ensures collect_tokens (step_ownleaf_transit e place v s).control =
               collect_tokens s.control) =
  let before = OwnLeaf (OwnedTransit place v) in
  let after = OwnedTransit place v in
  assert (collect_tokens before = collect_tokens after);
  plug_tokens_congruent e after before;
  assert (step_ownleaf_transit e place v s).control = plug e after;
  assert s.control = plug e before

//@ THM: THM-008
//@ REQ-FULL: -
//@ REQ-PART: OWN-009
//@ SPEC: core-calculus.md §5.1, core-calculus.md §5.3
//@ RULE: R-Delta, R-OwnLeaf, R-OwnLeafPass, R-OwnLeafTransit
//@ REDEX: model/redex/tests/root-token-test.rkt
//@ ASSUMPTIONS: tok_inv
//@ SCOPE: R-OwnLeafTransit の遷移について、評価文脈は七つの構成子に限る
let ownleaf_transit_preserves_tok_inv (e:ctx) (place:nat) (v:value) (s:state)
  : Lemma
      (requires (tok_inv s /\
                 s.control = plug e (OwnLeaf (OwnedTransit place v))))
      (ensures (tok_inv (step_ownleaf_transit e place v s))) =
  ownleaf_transit_preserves_token_list e place v s;
  assert (tok_inv (step_ownleaf_transit e place v s))

//@ AUX: example OWN-009
let example_delta_acquire () : Lemma
  (ensures
    (let r = Apply [PrimVal "o-acquire" "acquire"; Resource 7] in
     let s:state = { control = plug EHole r; heap = []; roots = [];
                     ledger = []; trace = [] } in
     let after = step_delta_acquire EHole r s 0 in
     after.control = OwnedLeaf 0 (Resource 7) /\
     after.ledger = [(0, Available)] /\
     structural_tokens after = [0] /\ observed_tokens after = [])) =
  assert_norm
    (let r = Apply [PrimVal "o-acquire" "acquire"; Resource 7] in
     let s:state = { control = plug EHole r; heap = []; roots = [];
                     ledger = []; trace = [] } in
     let after = step_delta_acquire EHole r s 0 in
     after.control = OwnedLeaf 0 (Resource 7) /\
     after.ledger = [(0, Available)] /\
     structural_tokens after = [0] /\ observed_tokens after = [])

//@ AUX: example OWN-009
let example_ownleaf_fresh () : Lemma
  (ensures
    (let e = EScope "" EHole in
     let s:state = { control = plug e (OwnLeaf (Resource 1));
                     heap = []; roots = []; ledger = []; trace = [] } in
     let after = step_ownleaf e (Resource 1) s 0 in
     after.control = Scope "" (OwnedLeaf 0 (Resource 1)) /\
     after.ledger = [(0, Available)] /\
     structural_tokens after = [0] /\ observed_tokens after = [])) =
  assert_norm
    (let e = EScope "" EHole in
     let s:state = { control = plug e (OwnLeaf (Resource 1));
                     heap = []; roots = []; ledger = []; trace = [] } in
     let after = step_ownleaf e (Resource 1) s 0 in
     after.control = Scope "" (OwnedLeaf 0 (Resource 1)) /\
     after.ledger = [(0, Available)] /\
     structural_tokens after = [0] /\ observed_tokens after = [])

//@ AUX: example OWN-009
let example_ownleaf_pass () : Lemma
  (ensures
    (let e = EScope "" EHole in
     let v = Resource 1 in
     let s:state = { control = plug e (OwnLeaf (OwnedLeaf 4 v));
                     heap = []; roots = [];
                     ledger = [(4, Available)]; trace = [] } in
     let after = step_ownleaf_pass e 4 v
       s in
     after.control = Scope "" (OwnedLeaf 4 (Resource 1)) /\
     after.ledger = [(4, Available)] /\
     structural_tokens after = [4] /\ observed_tokens after = [])) =
  assert_norm
    (let e = EScope "" EHole in
     let v = Resource 1 in
     let s:state = { control = plug e (OwnLeaf (OwnedLeaf 4 v));
                     heap = []; roots = [];
                     ledger = [(4, Available)]; trace = [] } in
     let after = step_ownleaf_pass e 4 v s in
     after.control = Scope "" (OwnedLeaf 4 (Resource 1)) /\
     after.ledger = [(4, Available)] /\
     structural_tokens after = [4] /\ observed_tokens after = [])

//@ AUX: example OWN-009
let example_ownleaf_transit () : Lemma
  (ensures
    (let payload = Construct "Option (Owned Res)" "some"
                     [OwnedLeaf 4 (Resource 1)] in
     let transit = OwnedTransit 0 payload in
     let e = EScope "" EHole in
     let s:state = { control = plug e (OwnLeaf transit);
                     heap = [(0, payload)]; roots = [(0, RMoved)];
                     ledger = [(4, Available)]; trace = [] } in
     let after = step_ownleaf_transit e 0 transit
       s in
     after.control = Scope "" (OwnedTransit 0 payload) /\
     after.ledger = [(4, Available)] /\
     structural_tokens after = [4] /\ observed_tokens after = [])) =
  assert_norm
    (let payload = Construct "Option (Owned Res)" "some"
                    [OwnedLeaf 4 (Resource 1)] in
     let transit = OwnedTransit 0 payload in
     let e = EScope "" EHole in
     let s:state = { control = plug e (OwnLeaf transit);
                     heap = [(0, payload)]; roots = [(0, RMoved)];
                     ledger = [(4, Available)]; trace = [] } in
     let after = step_ownleaf_transit e 0 transit s in
     after.control = Scope "" (OwnedTransit 0 payload) /\
     after.ledger = [(4, Available)] /\
     structural_tokens after = [4] /\ observed_tokens after = [])
