module Topazolite.Surface

open FStar.List.Tot
open FStar.List.Tot.Properties

type sid = | UserSid : string -> sid | SyntheticSid : sid
type span = { sid: sid; startByte: nat; endByte: nat }

let span_ok (s: span) : bool = s.startByte <= s.endByte
let within (n: nat) (s: span) : bool = span_ok s && s.endByte <= n
let contains (p: span) (c: span) : bool =
  p.sid = c.sid && p.startByte <= c.startByte && c.endByte <= p.endByte

type tkind = | TkInt | TkStr | TkIdent | TkKw | TkPunct | TkNl | TkEof
type stok = { kind: tkind; span: span }

type diag = { code: string; primary: span }

type lex_result =
  | LexOk   : list stok -> lex_result
  | LexFail : diag -> lex_result

let mk_span (id: sid) (lo: nat) (hi: nat) : span =
  { sid = id; startByte = lo; endByte = hi }

let bounded_span (id: sid) (n: nat) (lo: nat) (hi: nat) : span =
  let lo' = if lo <= n then lo else n in
  let hi' = if hi <= n then hi else n in
  let end' = if lo' <= hi' then hi' else lo' in
  mk_span id lo' end'

val bounded_span_ok : id:sid -> n:nat -> lo:nat -> hi:nat -> Lemma
  (within n (bounded_span id n lo hi))
let bounded_span_ok id n lo hi = ()

let byte_nat (b: FStar.UInt8.t) : nat = FStar.UInt8.v b

let byte_is (b: FStar.UInt8.t) (n: nat) : bool = byte_nat b = n

let is_space (b: FStar.UInt8.t) : bool =
  byte_is b 32 || byte_is b 9

let is_digit (b: FStar.UInt8.t) : bool =
  byte_nat b >= 48 && byte_nat b <= 57

let is_ident_start (b: FStar.UInt8.t) : bool =
  (byte_nat b >= 65 && byte_nat b <= 90) ||
  (byte_nat b >= 97 && byte_nat b <= 122) ||
  byte_is b 95

let is_ident_rest (b: FStar.UInt8.t) : bool =
  is_ident_start b || is_digit b

let is_continuation (b: FStar.UInt8.t) : bool =
  byte_nat b >= 128 && byte_nat b <= 191

let utf8_length (b: FStar.UInt8.t) : option nat =
  let n = byte_nat b in
  if n < 128 then Some 1
  else if n >= 194 && n <= 223 then Some 2
  else if n >= 224 && n <= 239 then Some 3
  else if n >= 240 && n <= 244 then Some 4
  else None

let rec utf8_ok_at (i: nat) (bs: list FStar.UInt8.t) : Tot (option nat) (decreases bs) =
  match bs with
  | [] -> None
  | b0 :: [] ->
      let n0 = byte_nat b0 in
      if n0 < 128 then
        None
      else Some i
  | b0 :: b1 :: [] ->
      let n0 = byte_nat b0 in
      if n0 < 128 then utf8_ok_at (i + 1) (b1 :: [])
      else if n0 >= 194 && n0 <= 223 && is_continuation b1 then
        utf8_ok_at (i + 2) []
      else Some i
  | b0 :: b1 :: b2 :: [] ->
      let n0 = byte_nat b0 in
      if n0 < 128 then utf8_ok_at (i + 1) (b1 :: b2 :: [])
      else if n0 >= 194 && n0 <= 223 then
        if is_continuation b1 then utf8_ok_at (i + 2) (b2 :: []) else Some i
      else if n0 >= 224 && n0 <= 239 && is_continuation b1 && is_continuation b2 then
        if (n0 = 224 && byte_nat b1 < 160) ||
           (n0 = 237 && byte_nat b1 >= 160) then Some i
        else utf8_ok_at (i + 3) []
      else Some i
  | b0 :: b1 :: b2 :: b3 :: tl ->
      let n0 = byte_nat b0 in
      if n0 < 128 then utf8_ok_at (i + 1) (b1 :: b2 :: b3 :: tl)
      else if n0 >= 194 && n0 <= 223 then
        if is_continuation b1 then utf8_ok_at (i + 2) (b2 :: b3 :: tl) else Some i
      else if n0 >= 224 && n0 <= 239 && is_continuation b1 && is_continuation b2 then
        if (n0 = 224 && byte_nat b1 < 160) ||
           (n0 = 237 && byte_nat b1 >= 160) then Some i
        else utf8_ok_at (i + 3) (b3 :: tl)
      else if n0 >= 240 && n0 <= 244 && is_continuation b1 &&
              is_continuation b2 && is_continuation b3 then
        if (n0 = 240 && byte_nat b1 < 144) ||
           (n0 = 244 && byte_nat b1 >= 144) then Some i
        else utf8_ok_at (i + 4) tl
      else Some i

let utf8_ok (bs: list FStar.UInt8.t) : Tot (option nat) = utf8_ok_at 0 bs

type bytes_split = {
  taken: list FStar.UInt8.t;
  remaining: list FStar.UInt8.t
}

type pos_split = {
  pos: nat;
  remaining: list FStar.UInt8.t
}

let rec scan_ident
  (acc: list FStar.UInt8.t)
  (rest: list FStar.UInt8.t)
  : Tot (r:bytes_split{length r.remaining <= length rest}) (decreases rest) =
  match rest with
  | b :: tl ->
      if is_ident_rest b then scan_ident (b :: acc) tl
      else { taken = rev acc; remaining = rest }
  | [] -> { taken = rev acc; remaining = [] }

let rec scan_int
  (acc: list FStar.UInt8.t)
  (rest: list FStar.UInt8.t)
  : Tot (r:bytes_split{length r.remaining <= length rest}) (decreases rest) =
  match rest with
  | b :: tl ->
      if is_digit b then scan_int (b :: acc) tl
      else { taken = rev acc; remaining = rest }
  | [] -> { taken = rev acc; remaining = [] }

let rec skip_comment
  (j: nat) (rest: list FStar.UInt8.t)
  : Tot (r:pos_split{length r.remaining <= length rest}) (decreases rest) =
  match rest with
  | b :: tl ->
      if byte_is b 10 then { pos = j; remaining = rest }
      else skip_comment (j + 1) tl
  | [] -> { pos = j; remaining = [] }

let comment_start (rest: list FStar.UInt8.t) : bool =
  match rest with
  | b0 :: b1 :: _ -> byte_is b0 47 && byte_is b1 47
  | _ -> false

let rec scan_nl_run
  (j: nat) (rest: list FStar.UInt8.t) (fuel: nat{length rest < fuel})
  : Tot (r:pos_split{length r.remaining <= length rest}) (decreases fuel) =
  if fuel = 0 then FStar.Pervasives.false_elim ()
  else match rest with
       | b :: tl ->
           if is_space b || byte_is b 10 then
             scan_nl_run (j + 1) tl (fuel - 1)
           else if comment_start rest then
             let r = skip_comment (j + 2) (match rest with
                                           | _ :: _ :: tl2 -> tl2
                                           | _ -> []) in
             scan_nl_run r.pos r.remaining (fuel - 1)
           else { pos = j; remaining = rest }
       | [] -> { pos = j; remaining = [] }

let codepoint_end
  (j: nat) (rest: list FStar.UInt8.t) : Tot nat =
  match rest with
  | b :: _ ->
      (match utf8_length b with
       | Some k -> j + k
       | None -> j + 1)
  | [] -> j

type string_scan =
  | StringOk : nat -> list FStar.UInt8.t -> string_scan
  | StringFail : string -> nat -> nat -> string_scan

let rec scan_str
  (start: nat) (j: nat) (rest: list FStar.UInt8.t)
  : Tot (r:string_scan{
           match r with
           | StringOk _ rr -> length rr <= length rest
           | StringFail _ _ _ -> True}) (decreases rest) =
  match rest with
  | [] -> StringFail "E-SUR-003" start j
  | b :: tl ->
      if byte_is b 10 then StringFail "E-SUR-003" start j
      else if byte_is b 34 then StringOk (j + 1) tl
      else if byte_is b 92 then
        (match tl with
         | [] -> StringFail "E-SUR-003" start (j + 1)
         | c :: rest2 ->
             if byte_is c 10 then StringFail "E-SUR-003" start (j + 1)
             else if byte_is c 92 || byte_is c 34 ||
                     byte_is c 110 || byte_is c 116 then
               scan_str start (j + 2) rest2
             else StringFail "E-SUR-004" j (codepoint_end (j + 1) (c :: rest2)))
      else scan_str start (j + 1) tl

let keyword_word (word: list FStar.UInt8.t) : tkind =
  match word with
  | [a; b] ->
      if byte_is a 102 && byte_is b 110 then TkKw else TkIdent
  | [a; b; c] ->
      if (byte_is a 108 && byte_is b 101 && byte_is c 116) ||
         (byte_is a 109 && byte_is b 117 && byte_is c 116) ||
         (byte_is a 102 && byte_is b 111 && byte_is c 114) then TkKw
      else TkIdent
  | [a; b; c; d] ->
      if (byte_is a 116 && byte_is b 114 && byte_is c 117 && byte_is d 101) ||
         (byte_is a 116 && byte_is b 121 && byte_is c 112 && byte_is d 101) ||
         (byte_is a 105 && byte_is b 109 && byte_is c 112 && byte_is d 108) then TkKw
      else TkIdent
  | [a; b; c; d; e] ->
      if (byte_is a 99 && byte_is b 111 && byte_is c 110 &&
          byte_is d 115 && byte_is e 116) ||
         (byte_is a 102 && byte_is b 97 && byte_is c 108 &&
          byte_is d 115 && byte_is e 101) ||
         (byte_is a 116 && byte_is b 114 && byte_is c 97 &&
          byte_is d 105 && byte_is e 116) then TkKw
      else TkIdent
  | [a; b; c; d; e; f] ->
      if (byte_is a 100 && byte_is b 101 && byte_is c 114 &&
          byte_is d 105 && byte_is e 118 && byte_is f 101) ||
         (byte_is a 114 && byte_is b 101 && byte_is c 116 &&
          byte_is d 117 && byte_is e 114 && byte_is f 110) then TkKw
      else TkIdent
  | _ -> TkIdent

// 命題 5。Racket の lexer.rkt が予約する 12 語のそれぞれに TkKw を返す。
// 予約語を接頭辞に持つ語と、予約語より短い語は TkIdent のままである。
val keyword_word_reserved : unit -> Lemma
  (keyword_word [102uy; 110uy] == TkKw /\
   keyword_word [108uy; 101uy; 116uy] == TkKw /\
   keyword_word [109uy; 117uy; 116uy] == TkKw /\
   keyword_word [102uy; 111uy; 114uy] == TkKw /\
   keyword_word [116uy; 114uy; 117uy; 101uy] == TkKw /\
   keyword_word [116uy; 121uy; 112uy; 101uy] == TkKw /\
   keyword_word [105uy; 109uy; 112uy; 108uy] == TkKw /\
   keyword_word [99uy; 111uy; 110uy; 115uy; 116uy] == TkKw /\
   keyword_word [102uy; 97uy; 108uy; 115uy; 101uy] == TkKw /\
   keyword_word [116uy; 114uy; 97uy; 105uy; 116uy] == TkKw /\
   keyword_word [100uy; 101uy; 114uy; 105uy; 118uy; 101uy] == TkKw /\
   keyword_word [114uy; 101uy; 116uy; 117uy; 114uy; 110uy] == TkKw /\
   keyword_word [114uy; 101uy; 116uy; 117uy; 114uy; 110uy; 115uy] == TkIdent /\
   keyword_word [102uy; 111uy] == TkIdent)
let keyword_word_reserved () = ()

let punctuation (b: FStar.UInt8.t) : bool =
  byte_is b 123 || byte_is b 125 || byte_is b 40 || byte_is b 41 ||
  byte_is b 44 || byte_is b 58 || byte_is b 61 || byte_is b 46 ||
  byte_is b 124 || byte_is b 38 || byte_is b 33 ||
  byte_is b 60 || byte_is b 62

let rec scan_fuel
  (id: sid) (n: nat) (i: nat) (rest: list FStar.UInt8.t)
  (acc: list stok) (fuel: nat{length rest < fuel}) : Tot lex_result (decreases fuel) =
  if fuel = 0 then FStar.Pervasives.false_elim ()
  else match rest with
       | [] -> LexOk (rev ({ kind = TkEof; span = bounded_span id n n n } :: acc))
       | b :: tl ->
           if is_space b then scan_fuel id n (i + 1) tl acc (fuel - 1)
           else if comment_start rest then
             (match rest with
              | _ :: _ :: tl2 ->
                  let r = skip_comment (i + 2) tl2 in
                  scan_fuel id n r.pos r.remaining acc (fuel - 1)
              | _ -> FStar.Pervasives.false_elim ())
           else if byte_is b 10 then
             let r = scan_nl_run (i + 1) tl (length tl + 1) in
             scan_fuel id n r.pos r.remaining
               ({ kind = TkNl; span = bounded_span id n i r.pos } :: acc) (fuel - 1)
           else if is_digit b then
             let r = scan_int [] rest in
             let j = i + length r.taken in
             scan_fuel id n j r.remaining
               ({ kind = TkInt; span = bounded_span id n i j } :: acc) (fuel - 1)
           else if is_ident_start b then
             let r = scan_ident [] rest in
             let j = i + length r.taken in
             scan_fuel id n j r.remaining
               ({ kind = keyword_word r.taken; span = bounded_span id n i j } :: acc)
               (fuel - 1)
           else if punctuation b then
             scan_fuel id n (i + 1) tl
               ({ kind = TkPunct; span = bounded_span id n i (i + 1) } :: acc)
               (fuel - 1)
           else if byte_is b 34 then
             (match scan_str i (i + 1) tl with
              | StringOk j rr ->
                  scan_fuel id n j rr
                    ({ kind = TkStr; span = bounded_span id n i j } :: acc)
                    (fuel - 1)
              | StringFail code start j ->
                  LexFail { code = code; primary = bounded_span id n start j })
           else
             let j = codepoint_end i rest in
             LexFail { code = "E-SUR-002"; primary = bounded_span id n i j }

let scan
  (id: sid) (n: nat) (i: nat) (rest: list FStar.UInt8.t)
  (acc: list stok) : Tot lex_result (decreases rest) =
  scan_fuel id n i rest acc (length rest + 1)

val lex : id:sid -> bs:list FStar.UInt8.t -> Tot lex_result
let lex (id: sid) (bs: list FStar.UInt8.t) : Tot lex_result =
  match utf8_ok bs with
  | Some i -> LexFail { code = "E-SUR-001"; primary = bounded_span id (length bs) i (i + 1) }
  | None -> scan id (length bs) 0 bs []

let token_ok (id: sid) (n: nat) (t: stok) : prop =
  t.span.sid == id /\ within n t.span

let all_tokens_ok (id: sid) (n: nat) (ts: list stok) : prop =
  forall (t: stok). memP t ts ==> token_ok id n t

val all_tokens_ok_cons : id:sid -> n:nat -> t:stok -> ts:list stok -> Lemma
  (requires token_ok id n t /\ all_tokens_ok id n ts)
  (ensures all_tokens_ok id n (t :: ts))
let all_tokens_ok_cons id n t ts = ()

val all_tokens_ok_rev : id:sid -> n:nat -> ts:list stok -> Lemma
  (requires all_tokens_ok id n ts)
  (ensures all_tokens_ok id n (rev ts))
let all_tokens_ok_rev id n ts =
  let aux (t: stok) : Lemma (memP t (rev ts) ==> token_ok id n t) =
    rev_memP ts t in
  FStar.Classical.forall_intro aux

val scan_fuel_span_sound : id:sid -> n:nat -> i:nat -> rest:list FStar.UInt8.t
                         -> acc:list stok -> fuel:nat{length rest < fuel} -> Lemma
  (requires all_tokens_ok id n acc)
  (ensures (match scan_fuel id n i rest acc fuel with
            | LexOk toks -> all_tokens_ok id n toks
            | LexFail d -> d.primary.sid == id /\ within n d.primary))
  (decreases fuel)
let rec scan_fuel_span_sound id n i rest acc fuel =
  if fuel = 0 then FStar.Pervasives.false_elim ()
  else (match rest with
       | [] ->
           all_tokens_ok_cons id n
             { kind = TkEof; span = bounded_span id n n n } acc;
           all_tokens_ok_rev id n ({ kind = TkEof; span = bounded_span id n n n } :: acc)
       | b :: tl ->
           if is_space b then
             scan_fuel_span_sound id n (i + 1) tl acc (fuel - 1)
           else if comment_start rest then
             (match rest with
              | _ :: _ :: tl2 ->
                  let r = skip_comment (i + 2) tl2 in
                  scan_fuel_span_sound id n r.pos r.remaining acc (fuel - 1)
              | _ -> FStar.Pervasives.false_elim ())
           else if byte_is b 10 then
             let r = scan_nl_run (i + 1) tl (length tl + 1) in
             let t = { kind = TkNl; span = bounded_span id n i r.pos } in
             all_tokens_ok_cons id n t acc;
             scan_fuel_span_sound id n r.pos r.remaining (t :: acc) (fuel - 1)
           else if is_digit b then
             let r = scan_int [] rest in
             let j = i + length r.taken in
             let t = { kind = TkInt; span = bounded_span id n i j } in
             all_tokens_ok_cons id n t acc;
             scan_fuel_span_sound id n j r.remaining (t :: acc) (fuel - 1)
           else if is_ident_start b then
             let r = scan_ident [] rest in
             let j = i + length r.taken in
             let t = { kind = keyword_word r.taken; span = bounded_span id n i j } in
             all_tokens_ok_cons id n t acc;
             scan_fuel_span_sound id n j r.remaining (t :: acc) (fuel - 1)
           else if punctuation b then
             let t = { kind = TkPunct; span = bounded_span id n i (i + 1) } in
             all_tokens_ok_cons id n t acc;
             scan_fuel_span_sound id n (i + 1) tl (t :: acc) (fuel - 1)
           else if byte_is b 34 then
             (match scan_str i (i + 1) tl with
              | StringOk j rr ->
                  let t = { kind = TkStr; span = bounded_span id n i j } in
                  all_tokens_ok_cons id n t acc;
                  scan_fuel_span_sound id n j rr (t :: acc) (fuel - 1)
              | StringFail code start j ->
                  bounded_span_ok id n start j)
           else
             bounded_span_ok id n i (codepoint_end i rest))

val utf8_ok_offset : bs:list FStar.UInt8.t -> Lemma
  (match utf8_ok bs with
   | Some i -> i < length bs
   | None   -> True)

val utf8_ok_offset_at : i:nat -> bs:list FStar.UInt8.t -> Lemma
  (ensures (match utf8_ok_at i bs with
            | Some j -> i <= j /\ j < i + length bs
            | None   -> True))
  (decreases (length bs))
let rec utf8_ok_offset_at i bs =
  match bs with
  | [] -> ()
  | b0 :: [] -> ()
  | b0 :: b1 :: [] ->
      let n0 = byte_nat b0 in
      if n0 < 128 then utf8_ok_offset_at (i + 1) [b1]
      else if n0 >= 194 && n0 <= 223 && is_continuation b1 then
        utf8_ok_offset_at (i + 2) []
      else ()
  | b0 :: b1 :: b2 :: [] ->
      let n0 = byte_nat b0 in
      if n0 < 128 then utf8_ok_offset_at (i + 1) [b1; b2]
      else if n0 >= 194 && n0 <= 223 && is_continuation b1 then
        utf8_ok_offset_at (i + 2) [b2]
      else if n0 >= 224 && n0 <= 239 && is_continuation b1 &&
              is_continuation b2 &&
              not ((n0 = 224 && byte_nat b1 < 160) ||
                   (n0 = 237 && byte_nat b1 >= 160)) then
        utf8_ok_offset_at (i + 3) []
      else ()
  | b0 :: b1 :: b2 :: b3 :: tl ->
      let n0 = byte_nat b0 in
      if n0 < 128 then utf8_ok_offset_at (i + 1) (b1 :: b2 :: b3 :: tl)
      else if n0 >= 194 && n0 <= 223 && is_continuation b1 then
        utf8_ok_offset_at (i + 2) (b2 :: b3 :: tl)
      else if n0 >= 224 && n0 <= 239 && is_continuation b1 &&
              is_continuation b2 &&
              not ((n0 = 224 && byte_nat b1 < 160) ||
                   (n0 = 237 && byte_nat b1 >= 160)) then
        utf8_ok_offset_at (i + 3) (b3 :: tl)
      else if n0 >= 240 && n0 <= 244 && is_continuation b1 &&
              is_continuation b2 && is_continuation b3 &&
              not ((n0 = 240 && byte_nat b1 < 144) ||
                   (n0 = 244 && byte_nat b1 >= 144)) then
        utf8_ok_offset_at (i + 4) tl
      else ()

let utf8_ok_offset bs = utf8_ok_offset_at 0 bs

val scan_span_sound : id:sid -> n:nat -> i:nat -> rest:list FStar.UInt8.t
                    -> acc:list stok -> Lemma
  (requires i <= n /\ i + length rest == n /\
            (forall (t: stok). memP t acc ==>
              (t.span.sid == id /\ within n t.span)))
  (ensures (match scan id n i rest acc with
            | LexOk toks ->
                forall (t: stok). memP t toks ==>
                  (t.span.sid == id /\ within n t.span)
            | LexFail d -> d.primary.sid == id /\ within n d.primary))
  (decreases rest)
let scan_span_sound id n i rest acc =
  scan_fuel_span_sound id n i rest acc (length rest + 1)

val lex_span_sound : id:sid -> bs:list FStar.UInt8.t -> Lemma
  (match lex id bs with
   | LexOk toks ->
       forall (t: stok). memP t toks ==>
         (t.span.sid == id && within (length bs) t.span)
   | LexFail d -> d.primary.sid == id && within (length bs) d.primary)
let lex_span_sound id bs =
  match utf8_ok bs with
  | Some i -> utf8_ok_offset bs
  | None -> scan_span_sound id (length bs) 0 bs []

(* BIT-003。| と & は、それぞれ 1 字句の記号になる。 *)
let lex_bar_amp_ok () : Lemma
  (match lex SyntheticSid [124uy; 38uy] with
   | LexOk [a; b; e] -> a.kind = TkPunct && b.kind = TkPunct && e.kind = TkEof
   | _ -> false)
  = assert_norm
      (match lex SyntheticSid [124uy; 38uy] with
       | LexOk [a; b; e] -> a.kind = TkPunct && b.kind = TkPunct && e.kind = TkEof
       | _ -> false)

(* P2j。!、<、> はそれぞれ 1 字句の記号になる。 *)
let lex_bang_angle_ok () : Lemma
  (match lex SyntheticSid [33uy; 60uy; 62uy] with
   | LexOk [a; b; c; e] -> a.kind = TkPunct && b.kind = TkPunct && c.kind = TkPunct && e.kind = TkEof
   | _ -> false)
  = assert_norm
      (match lex SyntheticSid [33uy; 60uy; 62uy] with
       | LexOk [a; b; c; e] -> a.kind = TkPunct && b.kind = TkPunct && c.kind = TkPunct && e.kind = TkEof
       | _ -> false)

type dkind = | DBind | DFnDecl

type sexpr =
  | SInt      : span -> nat -> sexpr
  | SStr      : span -> string -> sexpr
  | SUnit     : span -> sexpr
  | SBool     : span -> bool -> sexpr
  | SVar      : span -> string -> sexpr
  | SReturn   : span -> sexpr -> sexpr
  | SFn       : span -> list (span & option sty) -> option sty -> option seffrow -> sexpr -> sexpr
  | SApply    : span -> sexpr -> list sexpr -> sexpr
  | SProj     : span -> sexpr -> (span & string) -> sexpr
  | SProjRec  : span -> sexpr -> list (span & string) -> sexpr
  | SRec      : span -> list (span & sexpr) -> sexpr
  | SBlock    : span -> list sdecl -> sexpr -> sexpr
and sty =
  | TName     : span -> string -> sty
  | TRec      : span -> list sty -> sty
  | TFn       : span -> list sty -> sty -> option seffrow -> sty
  | TUnion    : span -> sty -> sty -> sty
  | TInter    : span -> sty -> sty -> sty
  | TApp      : span -> span -> string -> list sty -> sty
and sdecl =
  | SDecl     : span -> dkind -> span -> list (span & sty) -> option sty -> option seffrow -> sexpr -> sdecl
and seffrow =
  | SEffRow   : span -> list sefflabel -> seffrow
and sefflabel =
  | SEffLabel : span -> string -> option sty -> sefflabel

type node = | NExpr : sexpr -> node | NTy : sty -> node | NDecl : sdecl -> node
            | NRow : seffrow -> node | NLabel : sefflabel -> node

let rec option_stys (ts: list (option sty)) : Tot (list sty) (decreases ts) =
  match ts with
  | [] -> []
  | None :: tl -> option_stys tl
  | Some t :: tl -> t :: option_stys tl

let span_of_expr (e: sexpr) : Tot span =
  match e with
  | SInt s _      -> s
  | SStr s _      -> s
  | SUnit s       -> s
  | SBool s _     -> s
  | SVar s _      -> s
  | SReturn s _   -> s
  | SFn s _ _ _ _ -> s
  | SApply s _ _  -> s
  | SProj s _ _   -> s
  | SProjRec s _ _ -> s
  | SRec s _      -> s
  | SBlock s _ _  -> s

let span_of_ty (t: sty) : Tot span =
  match t with
  | TName s _  -> s
  | TRec s _   -> s
  | TFn s _ _ _ -> s
  | TUnion s _ _ -> s
  | TInter s _ _ -> s
  | TApp s _ _ _ -> s

let span_of_decl (d: sdecl) : Tot span =
  match d with
  | SDecl s _ _ _ _ _ _ -> s

let span_of_row (r: seffrow) : Tot span =
  match r with
  | SEffRow s _ -> s

let span_of_label (l: sefflabel) : Tot span =
  match l with
  | SEffLabel s _ _ -> s

let span_of_node (n: node) : Tot span =
  match n with
  | NExpr e -> span_of_expr e
  | NTy t   -> span_of_ty t
  | NDecl d -> span_of_decl d
  | NRow r  -> span_of_row r
  | NLabel l -> span_of_label l

let kids_of_expr (e: sexpr) : Tot (list node) =
  match e with
  | SInt _ _      -> []
  | SStr _ _      -> []
  | SUnit _       -> []
  | SBool _ _     -> []
  | SVar _ _      -> []
  | SReturn _ e   -> [NExpr e]
  | SFn _ ps r row b ->
      map NTy (option_stys (map snd ps)) @
      (match r with None -> [] | Some t -> [NTy t]) @
      (match row with None -> [] | Some eff -> [NRow eff]) @ [NExpr b]
  | SApply _ f a  -> NExpr f :: map NExpr a
  | SProj _ e1 _  -> [NExpr e1]
  | SProjRec _ e1 _ -> [NExpr e1]
  | SRec _ fs     -> map NExpr (map snd fs)
  | SBlock _ ds t -> map NDecl ds @ [NExpr t]

let kids_of_ty (t: sty) : Tot (list node) =
  match t with
  | TName _ _  -> []
  | TRec _ fs  -> map NTy fs
  | TFn _ ps r row ->
      map NTy ps @ [NTy r] @ (match row with None -> [] | Some eff -> [NRow eff])
  | TUnion _ l r -> [NTy l; NTy r]
  | TInter _ l r -> [NTy l; NTy r]
  | TApp _ _ _ args -> map NTy args

let kids_of_decl (d: sdecl) : Tot (list node) =
  match d with
  | SDecl _ _ _ ps r row v ->
      map NTy (map snd ps) @
      (match r with None -> [] | Some t -> [NTy t]) @
      (match row with None -> [] | Some eff -> [NRow eff]) @ [NExpr v]

let kids_of_node (n: node) : Tot (list node) =
  match n with
  | NExpr e -> kids_of_expr e
  | NTy t   -> kids_of_ty t
  | NDecl d -> kids_of_decl d
  | NRow (SEffRow _ labels) -> map NLabel labels
  | NLabel (SEffLabel _ _ arg) -> (match arg with None -> [] | Some t -> [NTy t])

let hull (a b: span) : Tot span =
  { sid = a.sid;
    startByte = (if a.startByte <= b.startByte then a.startByte else b.startByte);
    endByte   = (if a.endByte >= b.endByte then a.endByte else b.endByte) }

// 名前と label の span は子の節点ではないので、wf が親への包含を直接検査する。
let rec spans_in (s: span) (ss: list span) : Tot bool (decreases ss) =
  match ss with
  | []      -> true
  | x :: tl -> contains s x && spans_in s tl

let rec hull_all (s0: span) (ks: list node) : Tot span (decreases ks) =
  match ks with
  | []      -> s0
  | k :: tl -> hull_all (hull s0 (span_of_node k)) tl

let rec all_sid (i: sid) (ks: list node) : Tot bool (decreases ks) =
  match ks with
  | []      -> true
  | k :: tl -> (span_of_node k).sid = i && all_sid i tl

let rec all_span_ok (ks: list node) : Tot bool (decreases ks) =
  match ks with
  | []      -> true
  | k :: tl -> span_ok (span_of_node k) && all_span_ok tl

val hull_mono : a:span -> b:span -> Lemma
  (requires span_ok a /\ span_ok b /\ a.sid = b.sid)
  (ensures span_ok (hull a b) /\ (hull a b).sid = a.sid /\
           contains (hull a b) a /\ contains (hull a b) b)
let hull_mono a b = ()

val contains_trans : a:span -> b:span -> c:span -> Lemma
  (requires contains a b /\ contains b c)
  (ensures contains a c)
let contains_trans a b c = ()

val hull_all_grows : s0:span -> ks:list node -> Lemma
  (ensures contains (hull_all s0 ks) s0)
  (decreases ks)
let rec hull_all_grows s0 ks =
  match ks with
  | []      -> ()
  | k :: tl ->
      hull_all_grows (hull s0 (span_of_node k)) tl;
      contains_trans (hull_all (hull s0 (span_of_node k)) tl)
                     (hull s0 (span_of_node k)) s0

val hull_all_contains : s0:span -> ks:list node -> Lemma
  (requires span_ok s0 /\ all_sid s0.sid ks /\ all_span_ok ks)
  (ensures forall (c: node). memP c ks ==> contains (hull_all s0 ks) (span_of_node c))
  (decreases ks)
let rec hull_all_contains s0 ks =
  match ks with
  | []      -> ()
  | k :: tl ->
      hull_mono s0 (span_of_node k);
      hull_all_grows (hull s0 (span_of_node k)) tl;
      contains_trans (hull_all (hull s0 (span_of_node k)) tl)
                     (hull s0 (span_of_node k)) (span_of_node k);
      hull_all_contains (hull s0 (span_of_node k)) tl

let rec wf_ty (t: sty) : Tot bool (decreases t) =
  match t with
  | TName _ _  -> true
  | TRec s fs  -> wf_tys s fs
  | TFn s ps r row ->
      wf_tys s ps && contains s (span_of_ty r) && wf_ty r && wf_opt_row s row
  | TUnion s l r -> contains s (span_of_ty l) && wf_ty l && contains s (span_of_ty r) && wf_ty r
  | TInter s l r -> contains s (span_of_ty l) && wf_ty l && contains s (span_of_ty r) && wf_ty r
  | TApp s h _ args -> contains s h && wf_tys s args
and wf_tys (s: span) (ts: list sty) : Tot bool (decreases ts) =
  match ts with
  | []      -> true
  | t :: tl -> contains s (span_of_ty t) && wf_ty t && wf_tys s tl
and wf_opt_row (s: span) (row: option seffrow) : Tot bool (decreases row) =
  match row with
  | None -> true
  | Some r -> contains s (span_of_row r) && wf_row r
and wf_row (r: seffrow) : Tot bool (decreases r) =
  match r with
  | SEffRow s labels -> wf_labels s labels
and wf_labels (s: span) (labels: list sefflabel) : Tot bool (decreases labels) =
  match labels with
  | [] -> true
  | label :: rest ->
      contains s (span_of_label label) && wf_label label && wf_labels s rest
and wf_label (label: sefflabel) : Tot bool (decreases label) =
  match label with
  | SEffLabel _ _ None -> true
  | SEffLabel s _ (Some t) -> contains s (span_of_ty t) && wf_ty t

let rec wf_expr (e: sexpr) : Tot bool (decreases e) =
  match e with
  | SInt _ _      -> true
  | SStr _ _      -> true
  | SUnit _       -> true
  | SBool _ _     -> true
  | SVar _ _      -> true
  | SReturn s e   -> contains s (span_of_expr e) && wf_expr e
  | SFn s ps r row b ->
      spans_in s (map fst ps)
      && wf_tys s (option_stys (map snd ps))
      && (match r with None -> true | Some t -> contains s (span_of_ty t) && wf_ty t)
      && wf_opt_row s row
      && contains s (span_of_expr b) && wf_expr b
  | SApply s f a  -> contains s (span_of_expr f) && wf_expr f && wf_exprs s a
  | SProj s e1 (sl, _) -> contains s sl && contains s (span_of_expr e1) && wf_expr e1
  | SProjRec s e1 ls -> spans_in s (map fst ls) && contains s (span_of_expr e1) && wf_expr e1
  | SRec s fs     -> wf_fields s fs
  | SBlock s ds t -> wf_decls s ds && contains s (span_of_expr t) && wf_expr t
and wf_exprs (s: span) (es: list sexpr) : Tot bool (decreases es) =
  match es with
  | []      -> true
  | e :: tl -> contains s (span_of_expr e) && wf_expr e && wf_exprs s tl
and wf_fields (s: span) (fs: list (span & sexpr)) : Tot bool (decreases fs) =
  match fs with
  | []            -> true
  | (sl, e) :: tl -> contains s sl && contains s (span_of_expr e) && wf_expr e && wf_fields s tl
and wf_decl (d: sdecl) : Tot bool (decreases d) =
  match d with
  | SDecl s k sx ps r row v ->
      contains s sx
      && spans_in s (map fst ps)
      && (match k with
          | DBind -> (match ps with [] -> true | _ -> false)
                     && (match row with None -> true | Some _ -> false)
          | DFnDecl -> true)
      && wf_tys s (map snd ps)
      && (match r with None -> true | Some t -> contains s (span_of_ty t) && wf_ty t)
      && wf_opt_row s row
      && contains s (span_of_expr v) && wf_expr v
and wf_decls (s: span) (ds: list sdecl) : Tot bool (decreases ds) =
  match ds with
  | []      -> true
  | d :: tl -> contains s (span_of_decl d) && wf_decl d && wf_decls s tl

let wf_node (n: node) : Tot bool =
  match n with
  | NExpr e -> wf_expr e
  | NTy t   -> wf_ty t
  | NDecl d -> wf_decl d
  | NRow r  -> wf_row r
  | NLabel l -> wf_label l

// DBind の SDecl は仮引数と row を持たない。Racket の SBind に対応しない形を拒む。
val wf_bind_shape : s:span -> sx:span -> ps:list (span & sty) -> r:option sty
  -> row:option seffrow -> v:sexpr -> Lemma
  (requires wf_decl (SDecl s DBind sx ps r row v))
  (ensures ps == [] /\ row == None)
let wf_bind_shape s sx ps r row v = ()

val wf_tys_elim : s:span -> ts:list sty -> c:node -> Lemma
  (requires wf_tys s ts)
  (ensures memP c (map NTy ts) ==> (contains s (span_of_node c) /\ wf_node c))
  (decreases ts)
let rec wf_tys_elim s ts c =
  match ts with
  | []      -> ()
  | t :: tl -> wf_tys_elim s tl c

val wf_labels_elim : s:span -> labels:list sefflabel -> c:node -> Lemma
  (requires wf_labels s labels)
  (ensures memP c (map NLabel labels) ==>
           (contains s (span_of_node c) /\ wf_node c))
  (decreases labels)
let rec wf_labels_elim s labels c =
  match labels with
  | [] -> ()
  | label :: rest -> wf_labels_elim s rest c

val wf_exprs_elim : s:span -> es:list sexpr -> c:node -> Lemma
  (requires wf_exprs s es)
  (ensures memP c (map NExpr es) ==> (contains s (span_of_node c) /\ wf_node c))
  (decreases es)
let rec wf_exprs_elim s es c =
  match es with
  | []      -> ()
  | e :: tl -> wf_exprs_elim s tl c

val wf_fields_elim : s:span -> fs:list (span & sexpr) -> c:node -> Lemma
  (requires wf_fields s fs)
  (ensures memP c (map NExpr (map snd fs)) ==> (contains s (span_of_node c) /\ wf_node c))
  (decreases fs)
let rec wf_fields_elim s fs c =
  match fs with
  | []      -> ()
  | _ :: tl -> wf_fields_elim s tl c

val wf_decls_elim : s:span -> ds:list sdecl -> c:node -> Lemma
  (requires wf_decls s ds)
  (ensures memP c (map NDecl ds) ==> (contains s (span_of_node c) /\ wf_node c))
  (decreases ds)
let rec wf_decls_elim s ds c =
  match ds with
  | []      -> ()
  | d :: tl -> wf_decls_elim s tl c

val parse_span_containment : n:node -> c:node -> Lemma
  (requires wf_node n /\ memP c (kids_of_node n))
  (ensures contains (span_of_node n) (span_of_node c) /\ wf_node c)
let parse_span_containment n c =
  match n with
  | NExpr (SInt _ _) | NExpr (SStr _ _) | NExpr (SUnit _)
  | NExpr (SBool _ _) | NExpr (SVar _ _) | NTy (TName _ _) -> ()
  | NExpr (SReturn s e) -> wf_exprs_elim s [e] c
  | NExpr (SProj _ _ _) -> ()
  | NExpr (SProjRec _ _ _) -> ()
  | NExpr (SFn s ps r row b) ->
      FStar.List.Tot.Properties.append_memP
        (map NTy (option_stys (map snd ps)))
        ((match r with None -> [] | Some t -> [NTy t]) @
         (match row with None -> [] | Some eff -> [NRow eff]) @ [NExpr b]) c;
      FStar.List.Tot.Properties.append_memP
        (match r with None -> [] | Some t -> [NTy t])
        ((match row with None -> [] | Some eff -> [NRow eff]) @ [NExpr b]) c;
      FStar.List.Tot.Properties.append_memP
        (match row with None -> [] | Some eff -> [NRow eff]) [NExpr b] c;
      wf_tys_elim s (option_stys (map snd ps)) c
  | NExpr (SApply s f a) -> wf_exprs_elim s a c
  | NExpr (SRec s fs) -> wf_fields_elim s fs c
  | NExpr (SBlock s ds t) ->
      FStar.List.Tot.Properties.append_memP (map NDecl ds) [NExpr t] c;
      wf_decls_elim s ds c
  | NTy (TRec s fs) -> wf_tys_elim s fs c
  | NTy (TApp s _ _ args) -> wf_tys_elim s args c
  | NTy (TFn s ps r row) ->
      FStar.List.Tot.Properties.append_memP
        (map NTy ps) ([NTy r] @ (match row with None -> [] | Some eff -> [NRow eff])) c;
      FStar.List.Tot.Properties.append_memP
        [NTy r] (match row with None -> [] | Some eff -> [NRow eff]) c;
      wf_tys_elim s ps c
  | NTy (TUnion _ _ _) | NTy (TInter _ _ _) -> ()
  | NDecl (SDecl s _ _ ps r row v) ->
      FStar.List.Tot.Properties.append_memP
        (map NTy (map snd ps))
        ((match r with None -> [] | Some t -> [NTy t]) @
         (match row with None -> [] | Some eff -> [NRow eff]) @ [NExpr v]) c;
      FStar.List.Tot.Properties.append_memP
        (match r with None -> [] | Some t -> [NTy t])
        ((match row with None -> [] | Some eff -> [NRow eff]) @ [NExpr v]) c;
      FStar.List.Tot.Properties.append_memP
        (match row with None -> [] | Some eff -> [NRow eff]) [NExpr v] c;
      wf_tys_elim s (map snd ps) c
  | NRow (SEffRow s labels) -> wf_labels_elim s labels c
  | NLabel (SEffLabel _ _ _) -> ()

type core =
  | CLit      : span -> core
  | CVar      : span -> core
  | CApply    : span -> core -> list core -> core
  | CProj     : span -> span -> core -> core
  | CRec      : span -> list (span & core) -> core
  | CFn       : span -> list span -> option seffrow -> core -> core
  | CConstruct: span -> string -> list core -> core
  | CLet      : span -> span -> core -> core -> core
  | CReturn   : span -> core -> core
  | CRecur    : span -> span -> list span -> seffrow -> core -> core -> core

let span_of_core (c: core) : Tot span =
  match c with
  | CLit s           -> s
  | CVar s           -> s
  | CApply s _ _     -> s
  | CProj s _ _      -> s
  | CRec s _         -> s
  | CFn s _ _ _      -> s
  | CConstruct s _ _ -> s
  | CLet s _ _ _     -> s
  | CReturn s _      -> s
  | CRecur s _ _ _ _ _ -> s

let one_to_one (e: sexpr) : Tot bool =
  match e with
  | SInt _ _     -> true
  | SStr _ _     -> true
  | SUnit _      -> true
  | SBool _ _    -> true
  | SVar _ _     -> true
  | SReturn _ _  -> true
  | SFn _ _ _ _ _ -> true
  | SApply _ _ _ -> true
  | SProj _ _ _  -> true
  | SProjRec _ _ _ -> false
  | SRec _ _     -> true
  | SBlock _ _ _ -> false

let row_or_empty (s: span) (row: option seffrow) : Tot seffrow =
  match row with
  | None   -> SEffRow s []
  | Some r -> r

// 多 field 射影の各欄は label span を Proj と Rec の両方へ運ぶ。
let rec proj_fields (s_recv: span) (ls: list (span & string))
  : Tot (list (span & core)) (decreases ls) =
  match ls with
  | []      -> []
  | (sl, _) :: tl -> (sl, CProj sl sl (CVar s_recv)) :: proj_fields s_recv tl

let rec lower_expr (e: sexpr) : Tot core (decreases e) =
  match e with
  | SInt s _      -> CLit s
  | SStr s _      -> CLit s
  | SUnit s       -> CConstruct s "unit" []
  | SBool s b     -> CConstruct s (if b then "true" else "false") []
  | SVar s _      -> CVar s
  | SReturn s e   -> CReturn s (lower_expr e)
  | SFn s ps _ row b -> CFn s (map fst ps) row (lower_expr b)
  | SApply s f a  -> CApply s (lower_expr f) (lower_exprs a)
  | SProj s e1 (sl, _) -> CProj s sl (lower_expr e1)
  | SProjRec s e1 ls ->
      CLet s (span_of_expr e1) (lower_expr e1) (CRec s (proj_fields (span_of_expr e1) ls))
  | SRec s fs     -> CRec s (lower_fields fs)
  | SBlock _ ds t -> lower_block ds (lower_expr t)
and lower_exprs (es: list sexpr) : Tot (list core) (decreases es) =
  match es with
  | []      -> []
  | e :: tl -> lower_expr e :: lower_exprs tl
and lower_fields (fs: list (span & sexpr)) : Tot (list (span & core)) (decreases fs) =
  match fs with
  | []            -> []
  | (sl, e) :: tl -> (sl, lower_expr e) :: lower_fields tl
and lower_block (ds: list sdecl) (tail: core) : Tot core (decreases ds) =
  match ds with
  | []      -> tail
  | d :: tl -> lower_decl d (lower_block tl tail)
and lower_decl (d: sdecl) (rest: core) : Tot core (decreases d) =
  match d with
  | SDecl s DBind sx _ _ _ v ->
      CLet (hull s (span_of_core rest)) sx (lower_expr v) rest
  | SDecl s DFnDecl sx ps _ row v ->
      CRecur (hull s (span_of_core rest)) sx (map fst ps) (row_or_empty s row)
             (lower_expr v) rest

val lower_preserves_span : e:sexpr -> Lemma
  (requires one_to_one e)
  (ensures span_of_core (lower_expr e) == span_of_expr e)
let lower_preserves_span e =
  match e with
  | SInt _ _     -> ()
  | SStr _ _     -> ()
  | SUnit _      -> ()
  | SBool _ _    -> ()
  | SVar _ _     -> ()
  | SReturn _ _  -> ()
  | SFn _ _ _ _ _ -> ()
  | SApply _ _ _ -> ()
  | SProj _ _ _  -> ()
  | SProjRec _ _ _ -> ()
  | SRec _ _     -> ()
  | SBlock _ _ _ -> ()

// 命題 6。空でない block の根の span は先頭宣言と後続の根の hull である。
val lower_block_root_span : d:sdecl -> ds:list sdecl -> tail:core -> Lemma
  (span_of_core (lower_block (d :: ds) tail)
   == hull (span_of_decl d) (span_of_core (lower_block ds tail)))
let lower_block_root_span d ds tail =
  match d with
  | SDecl _ DBind _ _ _ _ _ -> ()
  | SDecl _ DFnDecl _ _ _ _ _ -> ()

// 命題 7。SFn は仮引数名の span と省略を含む row をそのまま運ぶ。
val lower_fn_fields : s:span -> ps:list (span & option sty) -> r:option sty
  -> row:option seffrow -> b:sexpr -> Lemma
  (lower_expr (SFn s ps r row b) == CFn s (map fst ps) row (lower_expr b))
let lower_fn_fields s ps r row b = ()

// 命題 7。SProj は label の span を運ぶ。
val lower_proj_label : s:span -> e1:sexpr -> l:(span & string) -> Lemma
  (lower_expr (SProj s e1 l) == CProj s (fst l) (lower_expr e1))
let lower_proj_label s e1 l = ()

// 命題 7。SRec の field label の span 列は元の列と等しい。
val lower_fields_labels : fs:list (span & sexpr) -> Lemma
  (ensures map fst (lower_fields fs) == map fst fs)
  (decreases fs)
let rec lower_fields_labels fs =
  match fs with
  | []      -> ()
  | _ :: tl -> lower_fields_labels tl

val lower_rec_labels : s:span -> fs:list (span & sexpr) -> Lemma
  (lower_expr (SRec s fs) == CRec s (lower_fields fs) /\
   map fst (lower_fields fs) == map fst fs)
let lower_rec_labels s fs = lower_fields_labels fs

// 命題 7。SProjRec の label span は field と Proj の両方へ運ぶ。
let proj_field_of (s_recv: span) (l: span & string) : Tot (span & core) =
  (fst l, CProj (fst l) (fst l) (CVar s_recv))

val proj_fields_spans : s_recv:span -> ls:list (span & string) -> Lemma
  (ensures proj_fields s_recv ls == map (proj_field_of s_recv) ls)
  (decreases ls)
let rec proj_fields_spans s_recv ls =
  match ls with
  | []      -> ()
  | _ :: tl -> proj_fields_spans s_recv tl

val lower_projrec_fields : s:span -> e1:sexpr -> ls:list (span & string) -> Lemma
  (lower_expr (SProjRec s e1 ls)
   == CLet s (span_of_expr e1) (lower_expr e1)
        (CRec s (map (proj_field_of (span_of_expr e1)) ls)))
let lower_projrec_fields s e1 ls = proj_fields_spans (span_of_expr e1) ls

// 命題 7。DBind は束縛名の span を持つ CLet になる。
val lower_decl_bind : s:span -> sx:span -> ps:list (span & sty) -> r:option sty
  -> row:option seffrow -> v:sexpr -> rest:core -> Lemma
  (lower_decl (SDecl s DBind sx ps r row v) rest
   == CLet (hull s (span_of_core rest)) sx (lower_expr v) rest)
let lower_decl_bind s sx ps r row v rest = ()

// 命題 7。DFnDecl は後続を含む CRecur になる。
val lower_decl_fn : s:span -> sx:span -> ps:list (span & sty) -> r:option sty
  -> row:option seffrow -> v:sexpr -> rest:core -> Lemma
  (lower_decl (SDecl s DFnDecl sx ps r row v) rest
   == CRecur (hull s (span_of_core rest)) sx (map fst ps)
             (row_or_empty s row) (lower_expr v) rest)
let lower_decl_fn s sx ps r row v rest = ()
