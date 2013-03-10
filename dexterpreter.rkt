#lang racket

; CESK state machine
;   control: a sequence of statements (stmts)
;   environment: frame pointer to this state machine (fp)
;   store: map of addr->values (store)
;   continuation: a seq of frames denoting procedure return contexts and
;                 exception handlers for this machine (kont)
(struct state {stmts fp stor kont})

; ρ : env = symbol -> addr
; σ : store = addr -> value
; value = integer + boolean + clo + cont
; clo ::= (clo <lam> <env>)
; κ : kont ::= (letk <var> <exp> <env> <kont>)
;           |  halt
; cont ::= (cont <kont>)
; addr = a set of unique addresses;
;        for this machine, symbols work;
;        gensym can create fresh addresses

; lookup the value of the framepointer, variable
(define (lookup σ fp var)
    (hash-ref σ `(,fp ,var)))

; extend store with one value
(define (extend σ fp var val)
    (hash-set! σ `(,fp ,var) val))

; extend store with one or more values
(define (extend* σ fp vars vals)
  (let ([$fp (gensym fp)])
    (match `(,vars ,vals)
      [`((,var . ,vars) (,val . ,vals))
            (extend σ $fp var val)
            (extend* σ fp vars vals)]
      [else σ])))

; global label store
(define label-stor (make-hash))

; update the label store
(define (extend-label-stor label stmt)
  (hash-set! label-stor label stmt))

; lookup the statement from the label in the store
(define (lookup-label label)
  (hash-ref label-stor label))

; Apply continuation
; Apply continuation
(define (apply/κ κ val σ)
  (match κ
    ; assignment continuation
    [`(,name ,next ,fp ,κ_)
        (let ([σ_ (extend σ fp name val)])
          (next fp σ_ κ_))]
    ; handle continuation
    [`(,classname ,label ,κ_) (apply/κ κ_ val σ)]
    ; the termination continuation
    ['(halt) '()]))

(define (apply/method m name val exps fp σ κ s)
  (let* ([fp_ (gensym fp)]
         [σ_ (extend σ fp_ "$this" val)]
         [κ_ `(,name ,s ,fp ,κ)])
    (match m
      [`(def ,mname ,vars ,body)
        (map (lambda (v e)
               (extend σ_ fp_ v (atomic-eval e fp σ)))
             vars exps)])
    `(body ,fp_ ,σ_ ,κ_)))

; AExp X FP X Store -> Value
(define (atomic-eval aexp fp σ)
  (match aexp
    [(? atom?) aexp]
    [else (lookup σ fp aexp)]))

; A helper to determine if these are plain values
(define (atom? aexp)
  (match aexp
    [(? void?) #t]
    [(? null?) #t]
    [(? boolean?) #t]
    [(? integer?) #t]
    [else #f]))

(define (next state)
  ; extract the state struct's contents
  (let* ([stmts (state-stmts state)]
         [fp (state-fp state)]
         [σ (state-stor state)]
         [κ (state-kont state)]
         [current-stmt (first stmts)]
         [next-stmt (rest stmts)])
    (match current-stmt
      ; push and pop exception handlers
      [`(pushhandler ,name ,l)
        `(,next-stmt ,fp ,σ ,(cons `(,name ,l ,κ) κ))]
      [`(pophandler)
        `(,next-stmt ,fp ,σ ,(car κ))]
      ; return statement
      [`(return ,e) (apply/κ κ (atomic-eval e fp σ) σ)]
      ; method invocation
      [`(invoke ,e ,mname ,vars)
            (let* ([val (lookup σ fp "$this")]
                   [cname (match val
                            [`(,op ,cname) cname])]
                   [m '()]);(lookup/method cname mname)])
              (apply/method m cname val vars fp σ κ next-stmt))]
      ; new object creation/assignment
      [`(,varname new ,classname)
            (let* ([op_ `(object ,classname ,(gensym))]
                   [σ_ (extend σ fp varname op_)])
                (state next-stmt fp σ_ κ))]
      ; assignment
      [`(,varname ,aexp)
            (let* ([val (atomic-eval aexp fp σ)]
                   [σ_ (extend σ fp varname val)])
                (state next-stmt fp σ_ κ))]
      ; if-goto stmt
      [`(if ,e goto ,l)
        ;=>
        (if (atomic-eval e fp σ)
              (state (lookup-label l) fp σ κ)
              (state next-stmt fp σ κ))]
      ; goto stmt
      [`(goto ,l) (state (lookup-label l) fp σ κ)]
      ; skip stmt
      ['(nop) (state next-stmt fp σ κ)]
      ; label stmt
      [`(label ,l)
            (extend-label-stor l next-stmt)
            (state next-stmt fp σ κ)])))

(define (run state)
  (let ([step (next state)])
    (if (eq? 'halt (state-kont step))
        step
        (run step))))

; Opcodes we care about (in order):
; http://pallergabor.uw.hu/androidblog/dalvik_opcodes.html

; move
; return
; const
; monitor
; switch
; instance-of
; array-length
; new-array
; throw
; goto
; switch
; compare
; conditions/branches
; array get
; array put
; instance get
; instance put
; static get
; static put
; invoke
; conversion
; arithmetic operations
; arithmetic and store
; *-quick


; vim: tabstop=2 shiftwidth=2 softtabstop=2
