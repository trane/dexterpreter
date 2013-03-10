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
  (hash-ref σ (fp, var)))

; extend store with one or more values
(define (extend* σ addrs vals)
  (match `(,addrs ,vals)
    [`((,addr . ,addrs) (,val . ,vals))
     (define $addr (gensym '$addr))
     (hash-set! σ $addr val)
     (extend* (hash-set addr $addr) addrs vals)]))

; global label store
(define label-stor (make-hash))

; update the label store
(define (extend-label-stor label stmt)
  (hash-set! label-stor label stmt))

; lookup the statement from the label in the store
(define (lookup-label label)
  (hash-ref label-stor label))

; Apply continuation
(define (apply-kont κ value σ)
  (match κ
    ; if this is the end, not sure what to return
    ['(halt) '()]
    ; otherwise, we need to get our new state
    [`(,f ,stmts ,fp ,kaddr)
      (let ([σ* (extend* σ fp (lookup σ fp value))])
          (state stmts σ* fp kaddr))]))

(define (atom? a)
  (match
    [(? void?) #t]
    [(? null?) #t]
    [(? boolean?) #t]
    [(? number?) #t]
    [else #f]))

(define (atomic-eval e fp σ)
  (match e
    [(? atom?) e]
    [(object ,classname ,op) (atomic-eval (lookup σ fp (op classname)))]
    [else (atomic-eval (lookup σ fp e))]))


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
