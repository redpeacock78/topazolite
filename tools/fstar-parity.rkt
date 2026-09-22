#lang racket

(provide (struct-out corr-row)
         racket-surface-constructors
         racket-ucore-constructors
         fstar-constructors
         correspondence-rows
         parity-errors
         main)

;; spec §10.2 のリスト 1。model/redex/surface.rkt の Surface の構成子名である。
(define racket-surface-constructors
  '(SProgram
    SBind SFnDecl STypeDecl
    SInt SStr SUnit SBool SVar SFn SApply SProj SProjRec SRec SBlock
    TName TRec TFn
    SName SParam SField SLabel TField))

;; spec §10.2 のリスト 2。model/redex/ucore.rkt の UCore+ のうち、
;; Surface の落とし込みが生成する形である。#:lit と #:var は keyword である。
(define racket-ucore-constructors
  '(#:lit #:var Apply Proj Rec Fn Construct Let Recur))

;; spec §10.2 のリスト 3。model/fstar/Topazolite.Surface.fst の構成子名である。
(define fstar-constructors
  '(SInt SStr SUnit SBool SVar SFn SApply SProj SProjRec SRec SBlock
    TName TRec TFn
    SDecl
    CLit CVar CApply CProj CRec CFn CConstruct CLet CRecur))

;; 対応表の 1 行。lefts は Racket 側の名前、rights は F* 側の名前である。
;; kind は 'one-to-one と 'many-to-one と 'none と 'excluded を採る。
;; 'excluded の行はリスト 1 から 3 に現れない名前を挙げてよい。
(struct corr-row (lefts rights kind) #:transparent)

(define (one-to-one left right) (corr-row (list left) (list right) 'one-to-one))
(define (no-counterpart left) (corr-row (list left) '() 'none))
(define (excluded left) (corr-row (list left) '() 'excluded))

;; spec §10.2 の対応表である。
(define correspondence-rows
  (list
   (one-to-one 'SInt 'SInt)
   (one-to-one 'SStr 'SStr)
   (one-to-one 'SUnit 'SUnit)
   (one-to-one 'SBool 'SBool)
   (one-to-one 'SVar 'SVar)
   (one-to-one 'SFn 'SFn)
   (one-to-one 'SApply 'SApply)
   (one-to-one 'SProj 'SProj)
   (one-to-one 'SProjRec 'SProjRec)
   (one-to-one 'SRec 'SRec)
   (one-to-one 'SBlock 'SBlock)
   (one-to-one 'TName 'TName)
   (one-to-one 'TRec 'TRec)
   (one-to-one 'TFn 'TFn)
   (corr-row '(SBind SFnDecl) '(SDecl) 'many-to-one)
   (no-counterpart 'STypeDecl)
   (no-counterpart 'SProgram)
   (no-counterpart 'SName)
   (no-counterpart 'SParam)
   (no-counterpart 'SField)
   (no-counterpart 'SLabel)
   (no-counterpart 'TField)
   (one-to-one '#:lit 'CLit)
   (one-to-one '#:var 'CVar)
   (one-to-one 'Apply 'CApply)
   (one-to-one 'Proj 'CProj)
   (one-to-one 'Rec 'CRec)
   (one-to-one 'Fn 'CFn)
   (one-to-one 'Construct 'CConstruct)
   (one-to-one 'Let 'CLet)
   (one-to-one 'Recur 'CRecur)
   (excluded 'stok)
   (excluded 'Suspend)
   (excluded 'Move)
   (excluded 'TypeMake)
   (excluded 'LetType)
   (excluded 'MacroCall)))

;; group-by は最初に現れた順を保つので、返る順序は入力の順に決まる。
(define (duplicate-names names)
  (for/list ([group (in-list (group-by values names))]
             #:when (> (length group) 1))
    (first group)))

;; kind ごとに左欄と右欄の数を決める。表の書き誤りをここで落とす。
(define (kind-arity-errors row)
  (define lefts (corr-row-lefts row))
  (define rights (corr-row-rights row))
  (define kind (corr-row-kind row))
  (case kind
    [(one-to-one)
     (append
      (if (= (length lefts) 1) '()
          (list (format "one-to-one の行 ~a の左欄が 1 つではない" lefts)))
      (if (= (length rights) 1) '()
          (list (format "one-to-one の行 ~a の右欄が 1 つではない" lefts))))]
    [(many-to-one)
     (append
      (if (>= (length lefts) 2) '()
          (list (format "many-to-one の行 ~a の左欄が 2 つ以上ではない" lefts)))
      (if (= (length rights) 1) '()
          (list (format "many-to-one の行 ~a の右欄が 1 つではない" lefts))))]
    [(none excluded)
     (append
      (if (= (length lefts) 1) '()
          (list (format "~a の行 ~a の左欄が 1 つではない" kind lefts)))
      (if (null? rights) '()
          (list (format "~a の行 ~a の右欄が空ではない" kind lefts))))]
    [else (list (format "~a は kind として認めない" kind))]))

;; 違反を決定的な順序で並べる。順序はリストの並びとこの手続きの並びで決まる。
;; 前半はリストから表への向き、後半は表からリストへの向きである。
;; 片側だけでは、表にだけ在る名前、綴りの誤り、左右の所属違い、kind と欄の
;; 数の食い違いが素通りする。
(define (parity-errors [surface racket-surface-constructors]
                       [ucore racket-ucore-constructors]
                       [fstar fstar-constructors]
                       [rows correspondence-rows])
  (define lefts (list->set (append-map corr-row-lefts rows)))
  (define rights (list->set (append-map corr-row-rights rows)))
  (define left-listed (list->set (append surface ucore)))
  (define right-listed (list->set fstar))
  (define listed (list->set (append surface ucore fstar)))
  (append
   (for/list ([name (in-list (duplicate-names surface))])
     (format "リスト 1 に ~a が重複している" name))
   (for/list ([name (in-list (duplicate-names ucore))])
     (format "リスト 2 に ~a が重複している" name))
   (for/list ([name (in-list (duplicate-names fstar))])
     (format "リスト 3 に ~a が重複している" name))
   (for/list ([name (in-list (append surface ucore))]
              #:unless (set-member? lefts name))
     (format "~a が対応表の左欄に無い" name))
   (for/list ([name (in-list fstar)]
              #:unless (set-member? rights name))
     (format "~a が対応表の右欄に無い" name))
   (for*/list ([row (in-list rows)]
               #:unless (eq? (corr-row-kind row) 'excluded)
               [name (in-list (corr-row-lefts row))]
               #:unless (set-member? left-listed name))
     (format "対応表の左欄の ~a がリスト 1 にもリスト 2 にも無い" name))
   (for*/list ([row (in-list rows)]
               [name (in-list (corr-row-rights row))]
               #:unless (set-member? right-listed name))
     (format "対応表の右欄の ~a がリスト 3 に無い" name))
   (for*/list ([row (in-list rows)]
               #:when (eq? (corr-row-kind row) 'excluded)
               [name (in-list (corr-row-lefts row))]
               #:when (set-member? listed name))
     (format "対象外の行の ~a がリスト 1 から 3 のどれかに在る" name))
   (append-map kind-arity-errors rows)))

(define (main [output (current-output-port)]
              [error-output (current-error-port)])
  (define errors (parity-errors))
  (cond
    [(null? errors)
     (fprintf output "Parity OK: Surface ~a / UCore+ ~a / F* ~a\n"
              (length racket-surface-constructors)
              (length racket-ucore-constructors)
              (length fstar-constructors))
     0]
    [else
     (for ([message (in-list errors)])
       (fprintf error-output "~a\n" message))
     1]))

(module+ main
  (exit (main)))
