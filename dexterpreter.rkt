#lang racket

; CESK state machine
;   control: a sequence of statements (stmts)
;   environment: frame pointer to this state machine (fp)
;   store: map of addr->values (store)
;   continuation: a seq of frames denoting procedure return contexts and
;                 exception handlers for this machine (kont)
(struct state {stmts fp stor kont})

(define-match-expander return
  (syntax-rule ()
    [(_ v)
     (or `(return ,v)
         `(return-wide ,v)
         `(return-object ,v))]))

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
(define (extend* σ fps vars vals)
    (map (λ (fp var val) (extend σ fp var val)) fps vars vals))

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
(define (apply-kont κ val σ)
  (match κ
    ; assignment continuation
    [`(,name ,next ,fp ,κ_)
        (let ([σ_ (extend σ fp name val)])
          (next fp σ_ κ_))]
    ; handle continuation
    [`(,classname ,label ,κ_) (apply-kont κ_ val σ)]
    ; the termination continuation
    ['(halt) ...]))

; AExp X FP X Store -> Value
(define (atomic-eval aexp fp σ)
  (match aexp
    [(? atom?) aexp]
    [else (lookup σ fp aexp)]))

; A helper to determine if these are plain values
(define (atom? aexp)
  (match
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
      ; return-{wide,object,}
      ; return only returns a value in a register vx, which is atomic
      [return (apply-kont κ vx σ)]
      [`(,varname ,aexp)
            (let* ([val (atomic-eval aexp fp σ)]
                   [σ_ (extend σ fp varname val)]
                (state next-stmt fp σ_ κ)))]
      [`(if ,e goto ,l)
        ;=>
        (if (atomic-eval e fp σ)
              (state (lookup-label l) fp σ κ)
              (state next-stmt fp σ κ))]
      [`(goto ,l) (state (lookup-label l) fp σ κ)]
      ['(nop) (state next-stmt fp σ κ)]
      [`(label ,l)
            (extend-label-stor l next-stmt)
            (state next-stmt fp σ κ)])))

(define (run state)
  (let ([step (next state)])
    (if (eq? 'halt (kont step))
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
