#lang racket

; CESK state machine
;   control: a sequence of statements (stmts)
;   environment: frame pointer to this state machine (fp)
;   store: map of addr->values (store)
;   continuation: a seq of frames denoting procedure return contexts and
;                 exception handlers for this machine (kont)
(struct state {stmts fp stor kont})
(define empty (make-hash))

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
(define label-stor (empty))

; update the label store
(define (extend-label-stor label stmt)
  (hash-set! label-stor label stmt))

; lookup the statement from the label in the store
(define (lookup-label label)
  (hash-ref label-stor label))

; class struct
;   super -> a super classname or void
;   fields := hash(field . var)
;   methods := hash(name . struct)
(struct class {super fields methods})
(struct method {params body})

(define class-table empty)

(define (extend-class-table name class)
  (hash-set! class-table name class))

(define (lookup/class name)
  (hash-ref class-table name))

; move up the class heir until you find a matching method
(define (lookup/method classname name)
  (let* ([class (lookup/class classname)]
         [methods (class-methods class)]
         [super (class-super class)])
    (if (hash-has-key? methods name)
        (hash-ref methods name)
        (if (void? (class-super class))
            (lookup/method (class-super class) name)
            (void)))))

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

; method application
(define (apply/method m name val exps fp σ κ s)
  (let* ([fp_ (gensym fp)]
         [σ_ (extend σ fp_ "$this" val)]
         [κ_ `(,name ,s ,fp ,κ)])
    (match m
      [`(def ,mname ,vars ,body)
        (map (lambda (v e)
               (extend σ_ fp_ v (eval/atomic e fp σ)))
             vars exps)])
    `(body ,fp_ ,σ_ ,κ_)))

; throw exception handler
(define (handle o fp σ ex)
  (match `(,o ,ex)
    [`((,op ,name) (,name_ ,l ,κ))  ; handler continuation
      (if (isinstanceof name_ name)
       `(,(lookup-label l) ,fp ,(extend σ fp "$ex" o) ,κ)
       (handle o fp σ kont))]  ; non-handler continuation
    [`(,val (,name ,s_ ,fp_ ,κ)) (handle val fp_ σ κ)]))


; AExp X FP X Store -> Value
(define (eval/atomic aexp ptr σ)
  (match aexp
    [(? atom?) aexp]
    [else (lookup σ ptr aexp)]))

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
      ; catch exceptions
      [`(move-exception ,e)
          (let ([$ex (lookup σ fp "$ex")])
            `(,next-stmt ,fp ,(extend σ fp $ex e)))]
      ; thrown exception
      [`(throw ,e) (handle (eval/atomic e fp σ) fp σ κ)]
      ; push and pop exception handlers
      [`(pushhandler ,name ,l)
        `(,next-stmt ,fp ,σ ,(cons `(,name ,l ,κ) κ))]
      [`(pophandler)
        `(,next-stmt ,fp ,σ ,(car κ))]
      ; return statement
      [`(return ,e) (apply/κ κ (eval/atomic e fp σ) σ)]
      ; method invocation
      [`(invoke ,e ,mname ,vars)
            (let* ([val (lookup σ fp "$this")]
                   [cname (match val
                            [`(,op ,cname) cname])]
                   [m (lookup/method cname mname)])
              (apply/method m cname val vars fp σ κ next-stmt))]
      ; new object creation/assignment
      [`(,varname new ,classname)
            (let* ([op_ `(object ,classname ,(gensym))]
                   [σ_ (extend σ fp varname op_)])
                (state next-stmt fp σ_ κ))]
      ; assignment
      [`(,varname ,aexp)
            (let* ([val (eval/atomic aexp fp σ)]
                   [σ_ (extend σ fp varname val)])
                (state next-stmt fp σ_ κ))]
      ; if-goto stmt
      [`(if ,e goto ,l)
        ;=>
        (if (eval/atomic e fp σ)
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
